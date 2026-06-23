//! The **deos-chat** gpui UI: a polished, dregg-pilled Matrix client — a room-list
//! sidebar with trust/encryption badges, a sender-grouped timeline with day
//! separators, reactions, replies, edit/redaction STATES, and the star feature
//! (membrane-bearing messages rendered as a "rehydrate a fork of the deos world"
//! card), plus typing + read-receipt indicators and a real `gpui-component`
//! composer (Enter=send, Shift-Enter=newline, ↑-to-edit-last).
//!
//! The view is pure presentation over the [`ChatSource`] seam — it does NOT know
//! whether the backend is the live `matrix-rust-sdk` worker, the world-backed
//! transport (`starbridge_v2::world_chat`, where the chat IS the dregg world), or
//! a recorded sync. The membrane affordances drive whatever the source exposes:
//! an executor-backed source (`membrane_capable`) mints/rehydrates/drives/stitches
//! REAL `Cell` frusta; a bare transport disables them — never a mock action.
//!
//! ## The dregg-pilling (the chat IS the dregg world, not a silo)
//!
//!   * **room = a cell** — the header shows the room's `RoomCell` (cell id +
//!     turn-count), so the conversation reads as the room cell's *history*
//!     (`docs/deos/APPS-AS-CELLS.md` §3).
//!   * **identity = a cell** — each sender carries an `IdentityCell` trust badge
//!     ("verify the person, not the device" — nheko). A CHANGED identity is
//!     surfaced loudly.
//!   * **send = a turn** — the composer's send returns a `SendReceipt`, shown in
//!     the status line ("turn N · cell:… · root …").
//!   * **a message carries a membrane** — the STAR feature: a message can embed a
//!     rehydratable cap-bounded fork of the deos world. The composer's "⬡ attach
//!     membrane" mints a REAL one from the source's executor (the comms-PD's live
//!     `World`) and sends it; a membrane-bearing message renders as a card with a
//!     live **rehydrate & drive** affordance that runs a real turn + stitch.
//!
//! ## Patterns adopted from nheko (the "solves problems correctly" reference)
//!
//!   * Composer keymap: Enter = send, Shift-Enter = newline (the de-facto
//!     standard); ↑ on an empty composer loads your last message to edit.
//!   * Timeline is a *presentation pass* over the event stream: sender-grouping,
//!     day separators, and trust badges are computed each frame, not stored.
//!     Edits/redactions are STATES of an event (an edited message shows "(edited)",
//!     a redacted one shows a tombstone) — never destructive deletions.
//!   * Legible trust: encryption is a per-room badge; person-trust is a per-sender
//!     badge.

use std::sync::Arc;

use gpui::prelude::FluentBuilder as _;
use gpui::{
    div, px, rgb, App, AppContext as _, Context, Entity, FocusHandle, Focusable, Hsla,
    InteractiveElement as _, IntoElement, MouseButton, ParentElement as _, Render, SharedString,
    StatefulInteractiveElement as _, Styled as _, Subscription, Window,
};
use gpui_component::{
    input::{Input, InputEvent, InputState},
    h_flex, v_flex, ActiveTheme as _,
};

use crate::cell::PersonTrust;
use crate::client::{EventState, MessageKind, RoomSummary, TimelineMessage};
use crate::source::ChatSource;

/// How many recent messages to pull per room.
const TIMELINE_LIMIT: u16 = 80;

/// The root chat view: sidebar + timeline + composer, over a [`ChatSource`].
pub struct ChatView {
    source: Arc<dyn ChatSource>,
    me: Option<String>,
    rooms: Vec<RoomSummary>,
    /// Index into `rooms` of the selected room, if any.
    selected: Option<usize>,
    /// The selected room's timeline (oldest-first).
    timeline: Vec<TimelineMessage>,
    /// The composer's rope-backed input (a real `gpui-component` `Input`).
    composer: Entity<InputState>,
    status: SharedString,
    /// If set, the composer is editing the event with this id (↑-to-edit), shown
    /// as an "editing…" banner over the composer.
    editing: Option<String>,
    focus: FocusHandle,
    _subs: Vec<Subscription>,
}

impl ChatView {
    /// Build the view over a data source. Loads the room list immediately and
    /// selects the first room so the demo opens onto a populated timeline.
    pub fn new(source: Arc<dyn ChatSource>, window: &mut Window, cx: &mut Context<Self>) -> Self {
        let composer = cx.new(|cx| {
            InputState::new(window, cx)
                .multi_line(true)
                .placeholder("Message — Enter to send, Shift-Enter for newline, ↑ to edit last")
        });

        // The load-bearing seam: Enter (without shift) submits; Shift-Enter is a
        // newline (handled by the input itself). This is nheko's composer contract.
        let subs = vec![cx.subscribe_in(
            &composer,
            window,
            |this, _input, event: &InputEvent, window, cx| {
                if let InputEvent::PressEnter { shift, .. } = event {
                    if !shift {
                        this.submit(window, cx);
                    }
                }
            },
        )];

        let me = source.whoami();
        let label = source.backend_label();
        let mut me_view = Self {
            source,
            me,
            rooms: Vec::new(),
            selected: None,
            timeline: Vec::new(),
            composer,
            status: SharedString::from(format!("connected — {label}")),
            editing: None,
            focus: cx.focus_handle(),
            _subs: subs,
        };
        me_view.refresh_rooms(cx);
        if !me_view.rooms.is_empty() {
            me_view.select_room(0, cx);
        }
        me_view
    }

    /// Pull the room list from the source.
    fn refresh_rooms(&mut self, cx: &mut Context<Self>) {
        match self.source.rooms() {
            Ok(rooms) => self.rooms = rooms,
            Err(e) => self.status = SharedString::from(format!("room list error: {e}")),
        }
        cx.notify();
    }

    /// Select a room by index and load its timeline.
    fn select_room(&mut self, idx: usize, cx: &mut Context<Self>) {
        if idx >= self.rooms.len() {
            return;
        }
        self.selected = Some(idx);
        self.editing = None;
        self.refresh_timeline(cx);
    }

    /// Reload the selected room's timeline from the source.
    fn refresh_timeline(&mut self, cx: &mut Context<Self>) {
        let Some(idx) = self.selected else { return };
        let room_id = self.rooms[idx].room_id.to_string();
        match self.source.timeline(&room_id, TIMELINE_LIMIT) {
            Ok(tl) => self.timeline = tl,
            Err(e) => self.status = SharedString::from(format!("timeline error: {e}")),
        }
        cx.notify();
    }

    /// Send the composer's contents to the selected room, then clear + refresh.
    /// **send = a turn**: shows the resulting `SendReceipt` digest in the status.
    fn submit(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        let Some(idx) = self.selected else { return };
        let body = self.composer.read(cx).value().to_string();
        let body = body.trim().to_string();
        if body.is_empty() {
            return;
        }
        let room_id = self.rooms[idx].room_id.to_string();
        match self.source.send_turn(&room_id, &body) {
            Ok(receipt) => {
                self.composer.update(cx, |state, cx| state.set_value("", window, cx));
                self.editing = None;
                self.status = SharedString::from(format!("sent · {}", receipt.digest()));
                self.refresh_timeline(cx);
            }
            Err(e) => {
                self.status = SharedString::from(format!("send failed: {e}"));
                cx.notify();
            }
        }
    }

    /// Attach + send a membrane — the STAR feature. Mints a REAL cap-bounded fork
    /// of the deos world from the live executor (the "screenshot a moment") and
    /// sends it as a membrane-bearing message. Fail-closed if the source holds no
    /// executor — NO mock fallback; the affordance is simply unavailable.
    fn attach_membrane(&mut self, _window: &mut Window, cx: &mut Context<Self>) {
        let Some(idx) = self.selected else { return };
        let room_id = self.rooms[idx].room_id.to_string();
        // MINT from the real executor (the screenshot of the moment).
        let env = match self.source.mint_membrane(&room_id) {
            Ok(env) => env,
            Err(e) => {
                self.status = SharedString::from(format!("membrane mint unavailable: {e}"));
                cx.notify();
                return;
            }
        };
        let summary = env.text_fallback();
        match self.source.send_membrane(&room_id, "", env) {
            Ok(_id) => {
                self.status = SharedString::from(format!("⬡ membrane minted + sent — {summary}"));
                self.refresh_timeline(cx);
            }
            Err(e) => {
                self.status = SharedString::from(format!("membrane send failed: {e}"));
                cx.notify();
            }
        }
    }

    /// **Rehydrate a received membrane, drive a real turn, stitch it back** — the
    /// interactive receive side of the star feature. Calls through the source to
    /// the real executor; shows the settled outcome in the status. Fail-closed if
    /// the source holds no executor (NO mock).
    fn rehydrate_membrane(&mut self, event_id: String, cx: &mut Context<Self>) {
        let Some(m) = self.timeline.iter().find(|m| m.event_id == event_id) else { return };
        let Some(env) = m.membrane.clone() else { return };
        match self.source.rehydrate_drive_stitch(&env) {
            Ok(summary) => {
                self.status = SharedString::from(format!("▶ rehydrated + drove + stitched — {summary}"));
                self.refresh_timeline(cx);
            }
            Err(e) => {
                self.status = SharedString::from(format!("rehydrate unavailable: {e}"));
                cx.notify();
            }
        }
    }

    /// ↑-to-edit-last: if the composer is empty, load the local user's most recent
    /// (live, text) message into it for editing. nheko's composer affordance.
    fn edit_last(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        if !self.composer.read(cx).value().is_empty() {
            return; // only when empty — don't clobber a draft
        }
        let me = self.me.clone();
        let last = self.timeline.iter().rev().find(|m| {
            Some(m.sender.as_str()) == me.as_deref()
                && m.state != EventState::Redacted
                && m.kind == MessageKind::Text
        });
        if let Some(m) = last {
            let body = m.body.clone();
            let id = m.event_id.clone();
            self.composer.update(cx, |state, cx| state.set_value(&body, window, cx));
            self.editing = Some(id);
            self.status = SharedString::from("editing your last message — Enter to resubmit");
            cx.notify();
        }
    }

    // --- rendering --------------------------------------------------------

    fn render_sidebar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let selected = self.selected;
        let rows = self.rooms.iter().enumerate().map(|(i, room)| {
            let is_sel = selected == Some(i);
            let name = room.display_name.clone();
            let unread = room.unread_notifications;
            let enc = room.is_encrypted;
            let direct = room.is_direct;
            let members = room.joined_members;
            v_flex()
                .id(("room", i))
                .px_3()
                .py_2()
                .gap_1()
                .cursor_pointer()
                .when(is_sel, |d| d.bg(cx.theme().sidebar_accent))
                .hover(|d| d.bg(cx.theme().muted))
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev, _win, cx| this.select_room(i, cx)),
                )
                .child(
                    h_flex()
                        .gap_2()
                        .items_center()
                        // The room glyph: 🔒 encrypted, 👤 a DM, # a room.
                        .child(div().text_xs().child(if enc {
                            "🔒"
                        } else if direct {
                            "👤"
                        } else {
                            "#"
                        }))
                        .child(div().flex_1().font_weight(gpui::FontWeight::MEDIUM).truncate().child(name))
                        .when(unread > 0, |d| {
                            d.child(
                                div()
                                    .px_1p5()
                                    .rounded_full()
                                    .bg(rgb(0xE0457B))
                                    .text_color(rgb(0xFFFFFF))
                                    .text_xs()
                                    .child(format!("{unread}")),
                            )
                        }),
                )
                .when_some(room.topic.clone(), |d, topic| {
                    d.child(
                        div()
                            .text_xs()
                            .text_color(cx.theme().muted_foreground)
                            .truncate()
                            .child(topic),
                    )
                })
                .child(
                    div()
                        .text_xs()
                        .text_color(cx.theme().muted_foreground)
                        .child(format!("{members} members")),
                )
        });

        v_flex()
            .w(px(256.))
            .h_full()
            .bg(cx.theme().sidebar)
            .border_r_1()
            .border_color(cx.theme().border)
            .child(
                h_flex()
                    .px_3()
                    .py_2()
                    .border_b_1()
                    .border_color(cx.theme().border)
                    .items_center()
                    .justify_between()
                    .child(div().font_weight(gpui::FontWeight::BOLD).child("rooms"))
                    .when_some(self.me.clone(), |d, me| {
                        d.child(
                            div()
                                .text_xs()
                                .text_color(cx.theme().muted_foreground)
                                .child(short_sender(&me)),
                        )
                    }),
            )
            .child(
                v_flex()
                    .id("room-list")
                    .flex_1()
                    .min_h(px(0.))
                    .overflow_y_scroll()
                    .children(rows),
            )
    }

    fn render_timeline(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let me = self.me.clone();
        let theme = cx.theme();
        let muted = theme.muted_foreground;
        let foreground = theme.foreground;
        let card_bg = theme.secondary;
        let border = theme.border;
        let accent = theme.accent;
        let success = theme.success;
        let danger = theme.danger;
        let warning = theme.warning;

        // Presentation pass: group consecutive messages by the same sender and
        // insert day separators (computed, not stored). nheko's timeline shape.
        let mut prev_sender: Option<String> = None;
        let mut prev_day: Option<i64> = None;
        let source = self.source.clone();
        let rows = self.timeline.iter().enumerate().map(move |(i, m)| {
            let same_sender = prev_sender.as_deref() == Some(m.sender.as_str())
                && m.reply_to.is_none()
                && m.kind != MessageKind::Membrane
                && !matches!(m.kind, MessageKind::Object(_));
            prev_sender = Some(m.sender.clone());

            let day = (m.timestamp_ms / 86_400_000) as i64;
            let day_sep = if prev_day != Some(day) {
                prev_day = Some(day);
                Some(day_label(m.timestamp_ms))
            } else {
                None
            };

            let is_me = me.as_deref() == Some(m.sender.as_str());
            let sender_short = short_sender(&m.sender);
            let time = time_label(m.timestamp_ms);
            let color = sender_color(&m.sender);
            let trust = source.identity(&m.sender).trust;

            let mut block = v_flex().id(("msg", i)).px_3();
            if let Some(label) = day_sep {
                block = block.child(
                    h_flex().my_2().items_center().gap_2().justify_center().child(
                        div()
                            .px_2()
                            .text_xs()
                            .text_color(muted)
                            .child(label),
                    ),
                );
            }

            // Sender header (with avatar + trust badge) only on the first of a run.
            if !same_sender {
                block = block.child(
                    h_flex()
                        .mt_2()
                        .gap_2()
                        .items_center()
                        .child(avatar_chip(&sender_short, color))
                        .child(
                            div()
                                .font_weight(gpui::FontWeight::BOLD)
                                .text_color(if is_me { accent } else { color })
                                .child(sender_short.clone()),
                        )
                        .child(trust_badge(trust, success, warning, danger))
                        .child(div().text_xs().text_color(muted).child(time)),
                );
            }

            // The reply context (quoted preview), if any.
            if let Some(reply) = &m.reply_to {
                block = block.child(
                    h_flex()
                        .ml(px(36.))
                        .my_1()
                        .gap_2()
                        .child(div().w(px(2.)).bg(accent).rounded_full())
                        .child(
                            v_flex()
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(sender_color(&reply.sender))
                                        .child(short_sender(&reply.sender)),
                                )
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(muted)
                                        .truncate()
                                        .child(reply.preview.clone()),
                                ),
                        ),
                );
            }

            // The message body — by STATE: redacted = tombstone, edited = body +
            // "(edited)", membrane = the star card, otherwise the body.
            let body_el: gpui::AnyElement = match (m.state, &m.kind) {
                (EventState::Redacted, _) => div()
                    .ml(px(36.))
                    .italic()
                    .text_color(muted)
                    .child("⌫ message removed")
                    .into_any_element(),
                (_, MessageKind::Membrane) => {
                    self.membrane_card(m, card_bg, border, accent, foreground, muted, cx).into_any_element()
                }
                (_, MessageKind::Object(_)) => {
                    object_card(m, card_bg, border, accent, foreground, muted).into_any_element()
                }
                (state, kind) => {
                    let mut row = h_flex().ml(px(36.)).items_baseline().gap_1().child(
                        div()
                            .text_color(if *kind == MessageKind::Notice { muted } else { foreground })
                            .when(*kind == MessageKind::Emote, |d| d.italic())
                            .child(m.body.clone()),
                    );
                    if state == EventState::Edited {
                        row = row.child(div().text_xs().text_color(muted).child("(edited)"));
                    }
                    row.into_any_element()
                }
            };
            block = block.child(body_el);

            // Reactions (the aggregate pills).
            if !m.reactions.is_empty() {
                let me2 = me.clone();
                let pills = m.reactions.iter().enumerate().map(move |(ri, r)| {
                    let mine = r.mine(me2.as_deref());
                    div()
                        .id(("react", i * 100 + ri))
                        .px_1p5()
                        .py(px(1.))
                        .rounded_full()
                        .border_1()
                        .border_color(if mine { accent } else { border })
                        .when(mine, |d| d.bg(accent.opacity(0.18)))
                        .text_xs()
                        .child(format!("{} {}", r.key, r.count()))
                });
                block = block.child(h_flex().ml(px(36.)).mt_1().gap_1().children(pills));
            }

            block
        });

        v_flex()
            .id("timeline")
            .flex_1()
            .min_h(px(0.))
            .overflow_y_scroll()
            .py_2()
            .children(rows)
    }

    /// The typing + read-receipt strip below the timeline (ephemeral view-state).
    fn render_presence(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let muted = cx.theme().muted_foreground;
        let (typing, read_by) = match self.selected.and_then(|i| self.rooms.get(i)) {
            Some(r) => {
                let id = r.room_id.to_string();
                (self.source.typing(&id), self.source.read_by(&id))
            }
            None => (Vec::new(), Vec::new()),
        };
        let typing_txt = if typing.is_empty() {
            String::new()
        } else {
            let names: Vec<String> = typing.iter().map(|u| short_sender(u)).collect();
            format!("✍ {} typing…", names.join(", "))
        };
        let read_txt = if read_by.is_empty() {
            String::new()
        } else {
            format!("✓ read by {}", read_by.len())
        };
        h_flex()
            .px_3()
            .py(px(2.))
            .h(px(18.))
            .gap_3()
            .text_xs()
            .text_color(muted)
            .when(!typing_txt.is_empty(), |d| d.child(div().child(typing_txt)))
            .when(!read_txt.is_empty(), |d| d.child(div().child(read_txt)))
    }

    fn render_composer(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let disabled = self.selected.is_none();
        let editing = self.editing.is_some();
        v_flex()
            .border_t_1()
            .border_color(cx.theme().border)
            .p_2()
            .gap_1()
            .when(editing, |d| {
                d.child(
                    h_flex()
                        .px_1()
                        .gap_2()
                        .items_center()
                        .text_xs()
                        .text_color(cx.theme().accent)
                        .child("✎ editing your last message")
                        .child(
                            div()
                                .id("cancel-edit")
                                .cursor_pointer()
                                .text_color(cx.theme().muted_foreground)
                                .child("(esc/clear to cancel)"),
                        ),
                )
            })
            .child(div().h(px(64.)).child(Input::new(&self.composer).h_full()))
            .child(
                h_flex()
                    .justify_between()
                    .items_center()
                    .child(
                        div()
                            .text_xs()
                            .text_color(cx.theme().muted_foreground)
                            .child(if disabled {
                                SharedString::from("select a room to send")
                            } else {
                                self.status.clone()
                            }),
                    )
                    .child(
                        // The STAR feature: attach a rehydratable cap-bounded fork
                        // of the deos world. Mints a real (mock) membrane offline.
                        div()
                            .id("attach-membrane")
                            .px_2()
                            .py_1()
                            .rounded_md()
                            .bg(cx.theme().accent)
                            .text_color(cx.theme().accent_foreground)
                            .cursor_pointer()
                            .text_xs()
                            .font_weight(gpui::FontWeight::MEDIUM)
                            .child("⬡ attach membrane")
                            .on_mouse_down(
                                MouseButton::Left,
                                cx.listener(|this, _ev, win, cx| this.attach_membrane(win, cx)),
                            ),
                    ),
            )
    }
}

impl Focusable for ChatView {
    fn focus_handle(&self, _: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for ChatView {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let selected_room = self.selected.and_then(|i| self.rooms.get(i)).cloned();
        let header = selected_room
            .as_ref()
            .map(|r| r.display_name.clone())
            .unwrap_or_else(|| "deos-chat".to_string());
        let topic = selected_room.as_ref().and_then(|r| r.topic.clone());
        // room = a cell: show the room cell id + turn-count in the header.
        let cell_line = selected_room.as_ref().map(|r| {
            let rc = self.source.room_cell(&r.room_id.to_string());
            format!("cell:{} · {} turns · {}", rc.cell_id.short(), rc.turn_count,
                if r.is_encrypted { "🔒 e2e" } else { "plaintext" })
        });

        let sidebar = self.render_sidebar(cx);
        let timeline = self.render_timeline(cx);
        let presence = self.render_presence(cx);
        let composer = self.render_composer(cx);

        h_flex()
            .size_full()
            .track_focus(&self.focus)
            .key_context("ChatView")
            .bg(cx.theme().background)
            .text_color(cx.theme().foreground)
            // ↑-to-edit-last (nheko's composer affordance).
            .on_key_down(cx.listener(|this, ev: &gpui::KeyDownEvent, win, cx| {
                if ev.keystroke.key == "up" {
                    this.edit_last(win, cx);
                }
            }))
            .child(sidebar)
            .child(
                v_flex()
                    .flex_1()
                    .min_w(px(0.))
                    .h_full()
                    .child(
                        v_flex()
                            .px_3()
                            .py_2()
                            .border_b_1()
                            .border_color(cx.theme().border)
                            .child(div().font_weight(gpui::FontWeight::BOLD).child(header))
                            .when_some(topic, |d, t| {
                                d.child(
                                    div()
                                        .text_xs()
                                        .text_color(cx.theme().muted_foreground)
                                        .child(t),
                                )
                            })
                            .when_some(cell_line, |d, c| {
                                d.child(
                                    div()
                                        .text_xs()
                                        .text_color(cx.theme().accent)
                                        .child(c),
                                )
                            }),
                    )
                    .child(timeline)
                    .child(presence)
                    .child(composer),
            )
    }
}

// --- presentation helpers (the computed timeline pass) ----------------------

/// A small round avatar chip with the sender's initial on their stable hue.
fn avatar_chip(name: &str, color: Hsla) -> impl IntoElement {
    let initial = name.chars().next().unwrap_or('?').to_uppercase().to_string();
    div()
        .size(px(22.))
        .rounded_full()
        .bg(color.opacity(0.85))
        .text_color(gpui::white())
        .text_xs()
        .flex()
        .items_center()
        .justify_center()
        .child(initial)
}

/// The per-sender person-trust badge ("verify the person, not the device").
fn trust_badge(trust: PersonTrust, success: Hsla, warning: Hsla, danger: Hsla) -> impl IntoElement {
    let (color, glyph) = match trust {
        PersonTrust::Verified => (success, trust.glyph()),
        PersonTrust::Unverified => (warning, trust.glyph()),
        PersonTrust::Changed => (danger, trust.glyph()),
    };
    div()
        .px_1()
        .rounded_sm()
        .bg(color.opacity(0.18))
        .text_color(color)
        .text_xs()
        .child(glyph)
}

/// The STAR feature card: a membrane-bearing message rendered as a rehydratable
/// fork of the deos world, with the cut/cursor/root and a LIVE "rehydrate & drive"
/// affordance. The rehydrate button is wired to the real executor through the
/// source (`rehydrate_drive_stitch`); it is live only when the source holds the
/// executor (`membrane_capable`) AND the envelope is rehydratable. Otherwise it is
/// rendered disabled — never a mock action.
impl ChatView {
    fn membrane_card(
        &self,
        m: &TimelineMessage,
        bg: Hsla,
        border: Hsla,
        accent: Hsla,
        fg: Hsla,
        muted: Hsla,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let env = m.membrane.clone();
        let (cells, depth, h, root, rehydratable) = match &env {
            Some(e) => (
                e.cut.cell_count,
                e.cut.max_depth,
                e.cursor.height,
                hex8(&e.frustum_root),
                e.is_rehydratable(),
            ),
            None => (0, 0, 0, String::new(), false),
        };
        // The button is LIVE only when this source can drive the real executor AND
        // the envelope is a supported wire version. A capable-but-newer membrane is
        // disabled with the update prompt; an INCAPABLE source disables it with an
        // honest "open in deos" prompt (the chat-only/no-executor case) — never mock.
        let capable = self.source.membrane_capable();
        let live = capable && rehydratable;
        let event_id = m.event_id.clone();
        let button_id = SharedString::from(format!("rehydrate-{}", m.event_id));
        let (button_label, hint): (&str, &str) = if live {
            ("▶ rehydrate & drive", "drives real turns · stitches back fail-closed")
        } else if rehydratable && !capable {
            ("⬡ open in deos to rehydrate", "this chat surface holds no executor")
        } else {
            ("⨯ newer membrane — update deos", "this build cannot rehydrate it")
        };
        let mut button = div()
            .id(gpui::ElementId::Name(button_id))
            .px_2()
            .py_1()
            .rounded_md()
            .border_1()
            .border_color(border)
            .text_xs();
        if live {
            button = button
                .bg(accent)
                .text_color(gpui::white())
                .cursor_pointer()
                .child(button_label)
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev, _win, cx| {
                        this.rehydrate_membrane(event_id.clone(), cx)
                    }),
                );
        } else {
            button = button.text_color(muted).child(button_label);
        }
        v_flex()
            .ml(px(36.))
            .my_1()
            .p_2()
            .gap_1()
            .rounded_lg()
            .bg(bg)
            .border_1()
            .border_color(accent.opacity(0.5))
            .max_w(px(420.))
            .child(
                h_flex()
                    .gap_2()
                    .items_center()
                    .child(div().text_color(accent).child("⬡"))
                    .child(
                        div()
                            .font_weight(gpui::FontWeight::BOLD)
                            .text_color(fg)
                            .child("deos membrane"),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(muted)
                            .child("a cap-bounded fork of the world"),
                    ),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(muted)
                    .child(format!(
                        "{cells} cells · depth {depth} · cut@h{h} · root {root}…"
                    )),
            )
            .child(
                h_flex()
                    .gap_2()
                    .items_center()
                    .child(button)
                    .child(div().text_xs().text_color(muted).child(hint)),
            )
    }
}

/// Render a **dregg semantic object** card — the generalized membrane. Each kind
/// gets its own glyph, summary line, and affordance:
///   * cell → "open this cell"
///   * capability → "accept into your powerbox"
///   * transclusion → the live quoted value
///   * affordance → a fireable (cap-gated) button
///   * receipt → the receipt summary
/// Unknown/absent objects render their text fallback (fail-closed — the extraction
/// already refused unknown kinds, so we only reach here for known ones).
fn object_card(
    m: &TimelineMessage,
    bg: Hsla,
    border: Hsla,
    accent: Hsla,
    fg: Hsla,
    muted: Hsla,
) -> impl IntoElement {
    use crate::object::DreggObject;
    // The per-kind (glyph, title, summary, action-label, action-fireable).
    let (glyph, title, summary, action, fireable): (&str, &str, String, &str, bool) =
        match &m.object {
            Some(DreggObject::Cell(c)) => (
                "▢",
                "deos cell",
                format!("{} · {}:{}", c.label, c.cell_kind.as_deref().unwrap_or("cell"), c.cell_id.short()),
                "open cell",
                true,
            ),
            Some(DreggObject::Capability(c)) => (
                "🔑",
                "deos capability",
                format!("{} · {}", c.label, c.sturdyref),
                "accept into powerbox",
                true,
            ),
            Some(DreggObject::Transclusion(t)) => (
                "❝",
                "deos transclusion",
                format!("{}.{} = {} · bound {}…", t.source_cell.short(), t.field, t.value, hex8(&t.bound_root)),
                "re-resolve live",
                true,
            ),
            Some(DreggObject::Affordance(a)) => (
                "▶",
                "deos affordance",
                format!("{} · {} on {}", a.label, a.action, a.target_cell.short()),
                "fire (cap-gated)",
                true,
            ),
            Some(DreggObject::Receipt(r)) => (
                "✔",
                "deos receipt",
                format!("turn {} · {} · root {}…", r.turn_index, r.cell_id.short(), hex8(&r.post_root)),
                "verify",
                false,
            ),
            // A membrane object reaches the membrane_card path, not here; any other
            // shape renders just the body fallback.
            _ => ("◇", "deos object", m.body.clone(), "", false),
        };
    v_flex()
        .ml(px(36.))
        .my_1()
        .p_2()
        .gap_1()
        .rounded_lg()
        .bg(bg)
        .border_1()
        .border_color(accent.opacity(0.5))
        .max_w(px(420.))
        .child(
            h_flex()
                .gap_2()
                .items_center()
                .child(div().text_color(accent).child(glyph))
                .child(div().font_weight(gpui::FontWeight::BOLD).text_color(fg).child(title)),
        )
        .child(div().text_xs().text_color(muted).child(summary))
        .when(!action.is_empty(), |d| {
            d.child(
                div()
                    .id("object-action")
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .border_1()
                    .border_color(border)
                    .text_xs()
                    .when(fireable, |d| {
                        d.bg(accent).text_color(gpui::white()).cursor_pointer().child(action.to_string())
                    })
                    .when(!fireable, |d| d.text_color(muted).child(action.to_string())),
            )
        })
}

/// `@ember:deos.local` → `ember`.
fn short_sender(s: &str) -> String {
    s.trim_start_matches('@')
        .split(':')
        .next()
        .unwrap_or(s)
        .to_string()
}

/// A stable per-sender color (hash → hue) so a glance reads who-said-what.
fn sender_color(s: &str) -> Hsla {
    let mut h: u32 = 2166136261;
    for b in s.bytes() {
        h = (h ^ b as u32).wrapping_mul(16777619);
    }
    let hue = (h % 360) as f32 / 360.0;
    gpui::hsla(hue, 0.55, 0.62, 1.0)
}

fn time_label(ms: u64) -> String {
    let secs = (ms / 1000) % 86_400;
    let h = secs / 3600;
    let m = (secs % 3600) / 60;
    format!("{h:02}:{m:02}")
}

fn day_label(ms: u64) -> String {
    // A coarse, dependency-free day stamp (days since epoch). Good enough for the
    // separator; a real client would localize. Kept tiny on purpose.
    let day = ms / 86_400_000;
    format!("· day {day} ·")
}

fn hex8(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(8);
    for byte in &b[..4] {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_sender_strips_sigil_and_server() {
        assert_eq!(short_sender("@ember:deos.local"), "ember");
        assert_eq!(short_sender("plain"), "plain");
    }

    #[test]
    fn sender_color_is_stable() {
        assert_eq!(sender_color("@a:b"), sender_color("@a:b"));
    }

    #[test]
    fn time_label_formats_hh_mm() {
        // 1h 1m past midnight = 3660s = 3_660_000 ms.
        assert_eq!(time_label(3_660_000), "01:01");
    }

    #[test]
    fn hex8_is_eight_chars() {
        assert_eq!(hex8(&[0xab; 32]).len(), 8);
        assert_eq!(hex8(&[0xab; 32]), "abababab");
    }
}
