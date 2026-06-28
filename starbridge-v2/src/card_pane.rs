//! CARD PANE — mount a hyperdreggmedia CARD (a deos-js applet's view-tree) as a LIVE
//! cockpit surface, backed by the cockpit's REAL `World`.
//!
//! This is the visible counterpart to [`crate::agent_attach`]. Where `agent_attach`
//! proves the AGENT'S HANDS drive the live ledger headlessly, this proves the CARD —
//! the operator-facing applet view — renders as real gpui-component pixels IN the
//! cockpit, and its button fires a real verified turn on the SAME live `World` the
//! cockpit inspector reads.
//!
//! ## The seam it closes
//!
//! `deos-view` ([`deos_view::AppletView`]) already renders a deos-js applet's view-tree
//! to real gpui-component widgets — but over the EMBEDDED [`deos_js::Applet`] (which
//! mints its own throwaway single-cell world). The cockpit's live substance is the
//! ATTACHED applet ([`deos_js::AttachedApplet`]), whose `fire` commits THROUGH
//! [`crate::agent_attach::WorldSinkAdapter::live`] onto the operator's real cells.
//!
//! [`CardPane`] is the small weld: it walks the SAME `deos.ui.*` view-tree
//! ([`deos_view::ViewNode`], parsed by [`deos_view::parse_view_tree`] from the REAL
//! engine-produced JSON) into the SAME gpui-component vocabulary, but binds + fires
//! against the live `AttachedApplet`:
//!
//!   * a `bind` node re-reads the bound model slot off the LIVE ledger
//!     (`AttachedApplet::get_u64` → a witnessed read of the operator's real cell); and
//!   * a `button`'s `on_click` calls `AttachedApplet::fire` = ONE cap-gated verified
//!     turn committed through `World::commit_turn` onto the live ledger (a receipt that
//!     lands on the cockpit's own provenance log).
//!
//! The view-tree is AUTHORED gpui-free (the JS builds `deos.ui.*` data + `JSON.stringify`s
//! it into the applet's ephemeral view-state — NO turn), so a throwaway embedded engine
//! authors the tree, and the LIVE `AttachedApplet` is the substance the rendered widgets
//! drive. (The cap tooth still runs in deos-js before every committed fire.)

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, px, rgb, App, ClickEvent, Context, FontWeight, InteractiveElement, IntoElement,
    MouseButton, ParentElement, Render, SharedString, Styled, Window,
};
use gpui_component::button::{Button, ButtonVariants};
use gpui_component::label::Label;
use gpui_component::{h_flex, v_flex, ActiveTheme};

use deos_js::AttachedApplet;
use deos_view::{disclose, parse_view_tree, pill_display, Disclosure, ViewNode};

/// A shared, interior-mutable handle on the LIVE attached applet. The card reads the
/// model through it (a `bind` re-read off the live ledger) and a button's `on_click`
/// fires a verified turn through it (a real turn on the cockpit's World). One handle,
/// shared by every widget — the single sovereign cell behind the whole card.
pub type SharedAttached = Rc<RefCell<AttachedApplet>>;

/// **The read+fire SUBSTANCE a [`CardPane`] renders over** — the three operations the
/// renderer needs from a live card backing: read a bound model slot, read ephemeral
/// view-state, and fire an affordance as a real verified turn. Abstracting it lets ONE
/// exhaustive renderer ([`CardPane::node`]) drive two backings: the deos-js
/// [`AttachedApplet`] (the operator/agent + inspector cards) and the app-framework
/// [`crate::app_registry::AppCardSubstance`] (a launched starbridge-app's BESPOKE card,
/// whose buttons fire the app's real cap-gated verified turns through its
/// [`crate::app_worldspine::AppWorldSpine`]).
pub trait CardSubstance {
    /// Read the bound model slot off the live ledger (a `bind`/`gauge`/`slider`/… read).
    fn get_u64(&self, slot: usize) -> u64;
    /// Read an ephemeral view-state draft (an `input` field), if the backing keeps one.
    fn get_view(&self, key: &str) -> Option<String>;
    /// Fire an affordance as ONE real verified turn (a button's `{turn, arg}`). A cap
    /// refusal / executor reject is surfaced as the `Err` string (the live model simply
    /// does not advance).
    fn fire(&mut self, method: &str, arg: i64) -> Result<(), String>;
}

/// A shared, interior-mutable [`CardSubstance`] — what a [`CardPane`] holds and every
/// widget closure clones. One handle, shared by the whole card.
pub type CardSubstanceRef = Rc<RefCell<dyn CardSubstance>>;

impl CardSubstance for AttachedApplet {
    fn get_u64(&self, slot: usize) -> u64 {
        AttachedApplet::get_u64(self, slot)
    }
    fn get_view(&self, key: &str) -> Option<String> {
        AttachedApplet::get_view(self, key).map(str::to_string)
    }
    fn fire(&mut self, method: &str, arg: i64) -> Result<(), String> {
        AttachedApplet::fire(self, method, arg)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }
}

/// A launched starbridge-app's card backing fires through its [`AppWorldSpine`] (the
/// app-framework→World bridge), reads bound slots off the live World ledger, and keeps
/// no ephemeral view-state (its cards are pure server-state views).
#[cfg(feature = "app-registry")]
impl CardSubstance for crate::app_registry::AppCardSubstance {
    fn get_u64(&self, slot: usize) -> u64 {
        crate::app_registry::AppCardSubstance::get_u64(self, slot)
    }
    fn get_view(&self, _key: &str) -> Option<String> {
        None
    }
    fn fire(&mut self, method: &str, arg: i64) -> Result<(), String> {
        crate::app_registry::AppCardSubstance::fire(self, method, arg)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }
}

/// The cockpit surface that renders a deos-js CARD over the LIVE `World`. A real gpui
/// `Render` entity: open it in a (headless or windowed) window and it paints the card's
/// widgets, and a button fires a real verified turn on the live ledger.
pub struct CardPane {
    /// The live card substance (shared so button handlers fire live turns + binds
    /// re-read the live ledger) — a deos-js applet or a launched app's spine.
    applet: CardSubstanceRef,
    /// The extracted view-tree (the real `deos.ui.*` element-tree the JS authored).
    tree: ViewNode,
    /// A short title shown above the card (the surface chrome).
    title: String,
}

impl CardPane {
    /// Build a card pane from a shared live applet + its view-tree + a title. The
    /// [`SharedAttached`] coerces into the [`CardSubstanceRef`] the pane holds (a deos-js
    /// applet IS a [`CardSubstance`]).
    pub fn new(applet: SharedAttached, tree: ViewNode, title: impl Into<String>) -> Self {
        let applet: CardSubstanceRef = applet;
        Self {
            applet,
            // Mount the CLEAN newcomer projection (progressive disclosure): drop the
            // `props.adept` "see the bones" detail (raw hashes, slot indices), keeping the
            // friendly card. An `adept` host can opt up by mounting the raw tree.
            tree: disclose(&tree, Disclosure::Simple),
            title: title.into(),
        }
    }

    /// Build a card pane over an arbitrary [`CardSubstance`] — the generalization of
    /// [`Self::new`] used to mount a launched starbridge-app's BESPOKE card (over a
    /// [`crate::app_registry::AppCardSubstance`]), so its buttons fire the app's real
    /// verified turns through its spine.
    pub fn new_substance(
        substance: CardSubstanceRef,
        tree: ViewNode,
        title: impl Into<String>,
    ) -> Self {
        Self {
            applet: substance,
            // The clean newcomer projection (see [`Self::new`]).
            tree: disclose(&tree, Disclosure::Simple),
            title: title.into(),
        }
    }

    /// The shared live substance handle (for the caller to inspect receipts / the live
    /// ledger after a turn fires — the SAME backing the widgets drive).
    pub fn substance(&self) -> CardSubstanceRef {
        self.applet.clone()
    }

    /// **Replace the rendered view-tree** — the edit-from-within hook. After a
    /// [`deos_js::card_editor::ViewPatch`] re-folds the card's view document, the
    /// caller bridges the new tree to a [`ViewNode`] and swaps it in here, so the next
    /// paint draws the reshaped surface. The live applet (the substance binds/fires
    /// drive) is untouched — only the view changed (the view is data, not code).
    pub fn set_tree(&mut self, tree: ViewNode) {
        // Keep the same clean newcomer projection the constructors mount.
        self.tree = disclose(&tree, Disclosure::Simple);
    }

    /// The card's current rendered view-tree (read-only) — so a mount can re-derive
    /// the surface or assert its shape after a reshape.
    pub fn tree(&self) -> &ViewNode {
        &self.tree
    }

    /// Render one view-tree node into a gpui element. Recursive: containers render
    /// their children with the same vocabulary `deos_view::AppletView` uses, but a
    /// `bind` re-reads the LIVE ledger and a `button` fires a LIVE turn.
    fn node(&self, node: &ViewNode, _window: &mut Window, cx: &mut App) -> gpui::AnyElement {
        let theme_fg = cx.theme().foreground;
        match node {
            ViewNode::VStack(children) => {
                let mut col = v_flex().gap_2().p_3();
                for c in children {
                    col = col.child(self.node(c, _window, cx));
                }
                col.into_any_element()
            }
            ViewNode::Row(children) => {
                let mut row = h_flex().gap_2().items_center();
                for c in children {
                    row = row.child(self.node(c, _window, cx));
                }
                row.into_any_element()
            }
            ViewNode::Text(s) => Label::new(s.clone())
                .text_color(theme_fg)
                // Never let a constrained column squeeze a text row to zero height
                // (which overlaps the next line) — a label keeps its own line height.
                .flex_shrink_0()
                .into_any_element(),
            ViewNode::Bind { slot, label, fmt } => {
                // THE SIGNAL BINDING over the LIVE ledger — re-read the bound model slot
                // off the cockpit's real cell (the same witnessed read the JS closure
                // made, now through `AttachedApplet`). Immediate-mode: this re-runs every
                // render, so after a live turn the new value shows.
                let value = self.applet.borrow().get_u64(*slot);
                // CONSUMER-DELIGHT: an opaque key/hash paints SHORT + friendly
                // (`🦊 swift-fox` / `0x8bf3…a3d8` / `1,234,567`) instead of a 20-digit
                // decimal; `raw` keeps the plain decimal so a counter is unchanged. The
                // SAME `deos_view::fmt` formatter the native/web/discord renderers call.
                let shown = deos_view::fmt::format_value(value, *fmt);
                let text = if label.is_empty() {
                    shown
                } else {
                    format!("{label}{shown}")
                };
                Label::new(text)
                    .font_weight(FontWeight::BOLD)
                    .text_color(theme_fg)
                    .flex_shrink_0()
                    .into_any_element()
            }
            ViewNode::Button { label, turn, arg } => {
                // THE REAL LIVE TURN — a button's onClick fires the applet's affordance =
                // ONE cap-gated verified turn committed THROUGH `World::commit_turn` onto
                // the live ledger. The handler captures the shared live applet + the
                // (turn, arg) from the view-tree.
                let applet = self.applet.clone();
                let turn = turn.clone();
                let arg = *arg;
                Button::new(("deos-card-aff", label_hash(label)))
                    .primary()
                    .label(label.clone())
                    .on_click(move |_ev: &ClickEvent, _window, _cx| {
                        // Fire the verified turn on the live World. A cap refusal /
                        // executor reject is surfaced to stderr (the screenshot stays
                        // honest); the live model simply does not advance.
                        //
                        // GUARDED at the event boundary: gpui dispatches this click from a
                        // `nounwind` Obj-C callback, so a panic crossing it would
                        // `process::abort` the whole cockpit. The `fire` is Result-typed,
                        // but `applet.borrow_mut()` would PANIC if the shared applet were
                        // already borrowed (e.g. a re-entrant fire), so contain any panic
                        // as a logged no-op rather than abort the process.
                        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            if let Err(e) = applet.borrow_mut().fire(&turn, arg) {
                                eprintln!(
                                    "card-pane: live affordance '{turn}' did not commit: {e}"
                                );
                            }
                        }))
                        .map_err(|_| {
                            eprintln!(
                                "card-pane: live affordance '{turn}' PANICKED — contained \
                                 (no-op) instead of aborting (the gpui event boundary is \
                                 nounwind)."
                            );
                        });
                    })
                    .into_any_element()
            }
            ViewNode::Input {
                bind_view,
                fire_turn,
                submit_label,
            } => {
                // Ephemeral view-state (draft text) — NOT cell state. When `fire_turn` is set a
                // paired submit button parses the draft into the turn's `arg` and fires a REAL
                // verified turn on the live World (input → verified turn).
                let draft = self.applet.borrow().get_view(bind_view).unwrap_or_default();
                let field = h_flex()
                    .px_2()
                    .py_1()
                    .border_1()
                    .border_color(cx.theme().border)
                    .rounded(px(4.))
                    .child(Label::new(if draft.is_empty() {
                        format!("‹{bind_view}›")
                    } else {
                        draft.clone()
                    }));
                if fire_turn.is_empty() {
                    return field.into_any_element();
                }
                let applet = self.applet.clone();
                let turn = fire_turn.clone();
                let draft_arg = draft.trim().parse::<i64>().unwrap_or(0);
                let label = if submit_label.is_empty() {
                    "submit".to_string()
                } else {
                    submit_label.clone()
                };
                h_flex()
                    .gap_1()
                    .items_center()
                    .child(field)
                    .child(
                        Button::new((
                            "deos-card-input-submit",
                            label_hash(&format!("{fire_turn}:{label}")),
                        ))
                        .primary()
                        .label(label)
                        .on_click(
                            move |_ev: &ClickEvent, _window, _cx| {
                                guarded_fire(&applet, &turn, draft_arg);
                            },
                        ),
                    )
                    .into_any_element()
            }
            ViewNode::List(items) => {
                let mut col = v_flex().gap_1();
                for it in items {
                    col = col.child(self.node(it, _window, cx));
                }
                col.into_any_element()
            }
            ViewNode::Table(rows) => {
                let mut col = v_flex().gap_1().border_1().border_color(cx.theme().border);
                for r in rows {
                    col = col.child(self.node(r, _window, cx));
                }
                col.into_any_element()
            }

            // ── The RICHNESS EXPANSION (batch 1) — mirror `deos_view::render`'s arms, but
            //    bound + fired against the LIVE attached applet. ──────────────────────────
            ViewNode::Section {
                title,
                tag,
                children,
            } => {
                // A titled, bordered container — the uniform "styled section". `tag=="genuine"`
                // accents the border (the existing `props.tag` styling convention).
                let accent = if tag == "genuine" {
                    theme_fg
                } else {
                    cx.theme().border
                };
                let mut card = v_flex().gap_1().p_2().border_1().border_color(accent);
                if !title.is_empty() {
                    card = card.child(
                        Label::new(title.clone())
                            .font_weight(FontWeight::BOLD)
                            .text_color(theme_fg),
                    );
                }
                for c in children {
                    card = card.child(self.node(c, _window, cx));
                }
                card.into_any_element()
            }
            ViewNode::Tabs {
                tabs,
                selected_slot,
                select_turn,
                panels,
            } => {
                // The active tab index lives in a MODEL SLOT (read live off the ledger), so a
                // tab switch is a REAL cap-gated verified turn — reflective + replayable.
                let active = self.applet.borrow().get_u64(*selected_slot) as usize;
                // The tab strip: one Button per label, the active one `.primary()`; each fires
                // `select_turn` with `arg = its index` (a verified turn through the live applet).
                let mut strip = h_flex().gap_1();
                for (i, label) in tabs.iter().enumerate() {
                    let applet = self.applet.clone();
                    let turn = select_turn.clone();
                    let idx = i as i64;
                    let mut b =
                        Button::new(("deos-card-tab", label_hash(&format!("{select_turn}:{i}"))))
                            .label(label.clone());
                    if i == active {
                        b = b.primary();
                    }
                    strip = strip.child(b.on_click(move |_ev: &ClickEvent, _window, _cx| {
                        // Same nounwind-boundary guard as a `button` fire (the gpui Obj-C
                        // callback is `nounwind`; contain a re-entrant-borrow panic as a no-op).
                        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            if let Err(e) = applet.borrow_mut().fire(&turn, idx) {
                                eprintln!("card-pane: tab select '{turn}' did not commit: {e}");
                            }
                        }))
                        .map_err(|_| {
                            eprintln!(
                                "card-pane: tab select '{turn}' PANICKED — contained (no-op)."
                            );
                        });
                    }));
                }
                // card_pane reads slots immediate-mode (no bind cursor), so render ONLY the
                // selected panel; out-of-range falls back to the first.
                let shown = if active < panels.len() { active } else { 0 };
                let mut col = v_flex().gap_2().child(strip);
                if let Some(panel) = panels.get(shown) {
                    col = col.child(self.node(panel, _window, cx));
                }
                col.into_any_element()
            }
            ViewNode::Gauge { slot, max, label } => {
                // A bound progress / balance bar — reads its slot IMMEDIATE-MODE off the live
                // ledger. The fill width is `value / max`, clamped to `[0,1]`.
                let value = self.applet.borrow().get_u64(*slot);
                let ratio = if *max == 0 {
                    0.0
                } else {
                    (value as f64 / *max as f64).clamp(0.0, 1.0)
                };
                let track_w = 140.0_f32;
                let fill_w = (track_w as f64 * ratio) as f32;
                let text = if label.is_empty() {
                    format!("{value}/{max}")
                } else {
                    format!("{label}{value}/{max}")
                };
                v_flex()
                    .gap_1()
                    .child(Label::new(text).text_color(theme_fg))
                    .child(
                        div()
                            .w(px(track_w))
                            .h(px(8.))
                            .rounded(px(4.))
                            .bg(cx.theme().border)
                            .child(
                                div()
                                    .w(px(fill_w.max(0.0)))
                                    .h(px(8.))
                                    .rounded(px(4.))
                                    .bg(theme_fg),
                            ),
                    )
                    .into_any_element()
            }
            ViewNode::Divider => div()
                .h(px(1.))
                .w_full()
                .bg(cx.theme().border)
                .into_any_element(),

            // ── The RICHNESS EXPANSION batch 2 — mirror `deos_view::render`'s arms, but bound +
            //    fired against the LIVE attached applet (every fire guarded at the gpui boundary). ─
            ViewNode::Grid { cols, children } => {
                let mut grid = div().flex().flex_wrap().gap_2();
                let max_w = if *cols > 0 {
                    Some(px(((520.0 / *cols as f32) - 12.0).max(48.0)))
                } else {
                    None
                };
                for c in children {
                    let mut cell = div().child(self.node(c, _window, cx));
                    if let Some(w) = max_w {
                        cell = cell.max_w(w);
                    }
                    grid = grid.child(cell);
                }
                grid.into_any_element()
            }
            ViewNode::Breadcrumb { items } => {
                let mut row = h_flex().gap_1().items_center();
                for (i, crumb) in items.iter().enumerate() {
                    if i > 0 {
                        row = row.child(Label::new("→").text_color(cx.theme().muted_foreground));
                    }
                    if crumb.turn.is_empty() {
                        row = row.child(Label::new(crumb.label.clone()).text_color(theme_fg));
                    } else {
                        let applet = self.applet.clone();
                        let turn = crumb.turn.clone();
                        let arg = crumb.arg;
                        row = row.child(
                            Button::new((
                                "deos-card-crumb",
                                label_hash(&format!("{}:{}", crumb.turn, i)),
                            ))
                            .label(crumb.label.clone())
                            .on_click(
                                move |_ev: &ClickEvent, _window, _cx| {
                                    guarded_fire(&applet, &turn, arg);
                                },
                            ),
                        );
                    }
                }
                row.into_any_element()
            }
            ViewNode::Progress { value, max, label } => {
                let ratio = if *max == 0 {
                    0.0
                } else {
                    (*value as f64 / *max as f64).clamp(0.0, 1.0)
                };
                let track_w = 140.0_f32;
                let fill_w = (track_w as f64 * ratio) as f32;
                let text = if label.is_empty() {
                    format!("{value}/{max}")
                } else {
                    format!("{label}{value}/{max}")
                };
                v_flex()
                    .gap_1()
                    .child(Label::new(text).text_color(theme_fg))
                    .child(
                        div()
                            .w(px(track_w))
                            .h(px(8.))
                            .rounded(px(4.))
                            .bg(cx.theme().border)
                            .child(
                                div()
                                    .w(px(fill_w.max(0.0)))
                                    .h(px(8.))
                                    .rounded(px(4.))
                                    .bg(theme_fg),
                            ),
                    )
                    .into_any_element()
            }
            ViewNode::Pill {
                text,
                tag,
                slot,
                cases,
            } => {
                // A colored status badge. LIVE variant (the static-phase-word cure): when bound
                // to a `slot` with `cases`, read the slot IMMEDIATE-MODE off the live ledger and
                // map the value to its word + color (a phase slot → COMMIT/REVEAL/RESOLVED), via
                // the SAME `pill_display` resolver every renderer calls. No slot/cases → static.
                let (shown_text, shown_tag) = match slot {
                    Some(s) if !cases.is_empty() => {
                        let value = self.applet.borrow().get_u64(*s);
                        pill_display(text, tag, cases, value)
                    }
                    _ => (text.as_str(), tag.as_str()),
                };
                div()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(tag_color(shown_tag))
                    .child(Label::new(shown_text.to_string()).text_color(rgb(0xffffff)))
                    .into_any_element()
            }
            ViewNode::Icon { glyph, tag } => {
                let color = if tag.is_empty() {
                    theme_fg
                } else {
                    tag_color(tag)
                };
                Label::new(glyph.clone())
                    .text_color(color)
                    .into_any_element()
            }
            ViewNode::Menu { items } => {
                let mut col = v_flex()
                    .gap_0p5()
                    .p_1()
                    .border_1()
                    .border_color(cx.theme().border);
                for (i, item) in items.iter().enumerate() {
                    if item.enabled {
                        let applet = self.applet.clone();
                        let turn = item.turn.clone();
                        let arg = item.arg;
                        col = col.child(
                            Button::new((
                                "deos-card-menu",
                                label_hash(&format!("{}:{}", item.turn, i)),
                            ))
                            .label(item.label.clone())
                            .on_click(
                                move |_ev: &ClickEvent, _window, _cx| {
                                    guarded_fire(&applet, &turn, arg);
                                },
                            ),
                        );
                    } else {
                        col = col.child(
                            div()
                                .opacity(0.4)
                                .child(Label::new(item.label.clone()).text_color(theme_fg)),
                        );
                    }
                }
                col.into_any_element()
            }
            ViewNode::Halo {
                target_slot: _,
                handles,
            } => {
                let mut ring = div().flex().flex_wrap().gap_1().items_center();
                for (i, h) in handles.iter().enumerate() {
                    if h.enabled {
                        let applet = self.applet.clone();
                        let turn = h.turn.clone();
                        let arg = h.arg;
                        ring = ring.child(
                            Button::new((
                                "deos-card-halo",
                                label_hash(&format!("{}:{}", h.turn, i)),
                            ))
                            .label(h.glyph.clone())
                            .on_click(
                                move |_ev: &ClickEvent, _window, _cx| {
                                    guarded_fire(&applet, &turn, arg);
                                },
                            ),
                        );
                    } else {
                        ring = ring.child(
                            div()
                                .opacity(0.4)
                                .size(px(24.))
                                .rounded_full()
                                .bg(cx.theme().border)
                                .child(Label::new(h.glyph.clone()).text_color(theme_fg)),
                        );
                    }
                }
                ring.into_any_element()
            }
            ViewNode::Slider {
                slot,
                min,
                max,
                turn,
            } => {
                // A bound scrubber over the LIVE ledger: discrete clickable ticks (the same
                // actuation the native Time scrubber uses), each seeking `arg = its value`.
                let value = self.applet.borrow().get_u64(*slot);
                let lo = *min;
                let hi = (*max).max(lo + 1);
                let span = hi - lo;
                let n_ticks = span.clamp(1, 20) as usize;
                let mut track = h_flex().gap_0p5().items_center();
                for k in 0..=n_ticks {
                    let tick_val = lo + (span * k as u64) / n_ticks as u64;
                    let filled = tick_val <= value;
                    let applet = self.applet.clone();
                    let turn_s = turn.clone();
                    let seek = tick_val as i64;
                    track = track.child(
                        div()
                            .id(SharedString::from(format!("deos-card-slider-{slot}-{k}")))
                            .w(px(10.))
                            .h(px(16.))
                            .rounded(px(2.))
                            .bg(if filled { theme_fg } else { cx.theme().border })
                            .cursor_pointer()
                            .on_mouse_down(MouseButton::Left, move |_ev, _window, _cx| {
                                guarded_fire(&applet, &turn_s, seek);
                            }),
                    );
                }
                v_flex()
                    .gap_1()
                    .child(Label::new(format!("{lo} ≤ {value} ≤ {hi}")).text_color(theme_fg))
                    .child(track)
                    .into_any_element()
            }
            ViewNode::Toggle {
                slot,
                on_turn,
                off_turn,
                glyph_on,
                glyph_off,
                label,
            } => {
                let on = self.applet.borrow().get_u64(*slot) != 0;
                let glyph = if on {
                    glyph_on.clone()
                } else {
                    glyph_off.clone()
                };
                let applet = self.applet.clone();
                let fire = if on {
                    off_turn.clone()
                } else {
                    on_turn.clone()
                };
                let text = format!("{glyph} {label}");
                Button::new((
                    "deos-card-toggle",
                    label_hash(&format!("{on_turn}:{off_turn}:{slot}")),
                ))
                .label(text)
                .on_click(move |_ev: &ClickEvent, _window, _cx| {
                    if !fire.is_empty() {
                        guarded_fire(&applet, &fire, 0);
                    }
                })
                .into_any_element()
            }
            ViewNode::Tile { handle, w, h } => {
                let tw = if *w == 0 {
                    320.0
                } else {
                    (*w as f32).min(960.0)
                };
                let th = if *h == 0 {
                    200.0
                } else {
                    (*h as f32).min(720.0)
                };
                v_flex()
                    .w(px(tw))
                    .h(px(th))
                    .gap_1()
                    .items_center()
                    .justify_center()
                    .border_1()
                    .border_color(cx.theme().border)
                    .rounded(px(4.))
                    .bg(cx.theme().background)
                    .child(Label::new("▦").text_color(cx.theme().muted_foreground))
                    .child(
                        Label::new(format!("‹tile {handle}: host-painted region {w}×{h}›"))
                            .text_color(cx.theme().muted_foreground),
                    )
                    .into_any_element()
            }
            ViewNode::Host { cell, view } => {
                // The COMPOSITION KEYSTONE — mount a cell's WHOLE hosted view-tree as a
                // subtree. A bordered frame with a muted `⌂ <cell>` header; an UNRESOLVED host
                // paints an honest placeholder (it has no tree to mount yet).
                let head = format!("⌂ {}", short_cell(cell));
                let mut frame = v_flex()
                    .gap_1()
                    .p_2()
                    .border_1()
                    .border_color(cx.theme().border)
                    .child(
                        Label::new(head)
                            .text_color(cx.theme().muted_foreground)
                            .into_any_element(),
                    );
                match view {
                    Some(v) => frame = frame.child(self.node(v, _window, cx)),
                    None => {
                        frame = frame.child(
                            Label::new(format!("‹mount cell {}: unresolved›", short_cell(cell)))
                                .text_color(cx.theme().muted_foreground),
                        )
                    }
                }
                frame.into_any_element()
            }
            ViewNode::Adept(inner) => {
                // The progressive-disclosure marker. A `simple`-disclosed tree (the clean
                // newcomer default this pane mounts) drops these before they reach `node`, so
                // this arm only fires if an un-disclosed tree is rendered directly — then it is
                // TRANSPARENT (render the wrapped node) so the adept detail still paints.
                self.node(inner, _window, cx)
            }
        }
    }
}

/// Fire a live affordance through the attached applet, GUARDED at the gpui event boundary (the
/// Obj-C callback is `nounwind`, so a re-entrant-borrow panic would `process::abort` the whole
/// cockpit — contain it as a logged no-op instead). The shared weld every batch-2 actuating node
/// (menu / halo / slider / toggle / breadcrumb / input-submit) routes its click through.
fn guarded_fire(applet: &CardSubstanceRef, turn: &str, arg: i64) {
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        if let Err(e) = applet.borrow_mut().fire(turn, arg) {
            eprintln!("card-pane: live affordance '{turn}' did not commit: {e}");
        }
    }))
    .map_err(|_| {
        eprintln!("card-pane: live affordance '{turn}' PANICKED — contained (no-op).");
    });
}

/// The semantic-tag palette (mirrors `deos_view::render::tag_color`) — a `pill`/`icon` tag maps
/// to a tint (the cockpit's `pill(text, color)` idiom expressed as data).
fn tag_color(tag: &str) -> gpui::Hsla {
    let c = match tag {
        "good" | "genuine" | "live" => 0x3fb950,
        "warn" | "pending" => 0xd29922,
        "bad" | "refusal" | "revoked" => 0xf85149,
        "muted" => 0x9aa0aa,
        _ => 0x5b8cff, // accent
    };
    rgb(c).into()
}

/// Truncate a hex cell-id for a compact host header (mirrors `deos_view::render::short_cell`).
fn short_cell(cell: &str) -> String {
    if cell.len() > 12 {
        format!("{}…", &cell[..12])
    } else {
        cell.to_string()
    }
}

impl Render for CardPane {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let title = self.title.clone();
        let app: &mut App = cx;
        let header_fg = app.theme().muted_foreground;
        let border = app.theme().border;
        let background = app.theme().background;
        let foreground = app.theme().foreground;
        // Walk the view-tree by BORROW (`&self.tree`) — it can be a large `ViewNode`,
        // and a deep clone every paint is pure waste; `node` only reads it. `self` is
        // borrowed immutably here, `app` is `cx` (a distinct object), so the two
        // borrows don't conflict.
        let body = self.node(&self.tree, window, app);
        // SIZE TO CONTENT, NOT THE COLUMN. The card is a content-sized object: it
        // hugs its view-tree vertically (`w_full`, no `h_full`) so a host never sees
        // it stretch to fill the whole pane and leave a dead canvas below the content,
        // and so its flex children are never squeezed against an over-tall parent
        // (which collapsed line heights into overlapping text). The HOST decides the
        // frame; the card draws exactly as tall as it is.
        div().w_full().bg(background).text_color(foreground).child(
            // The surface chrome — a titled card frame so it reads as a cockpit pane.
            v_flex()
                .w_full()
                .child(
                    div().px_3().py_2().border_b_1().border_color(border).child(
                        Label::new(title)
                            .font_weight(FontWeight::BOLD)
                            .text_color(header_fg),
                    ),
                )
                .child(body),
        )
    }
}

/// Author a card's view-tree by running `applet_js` in real SpiderMonkey against the
/// LIVE attached applet, then extract the engine-produced `deos.ui.*` tree.
///
/// The JS MUST build a `deos.ui.*` tree and stash it under [`deos_view::view_tree_key`]
/// via `app.view.set(...)` (ephemeral view-state — NO turn). The view-tree build commits
/// NOTHING; only a button's later `fire` does. The driven [`AttachedApplet`] is handed
/// back (its `WorldSink` reads + commits onto the live World) paired with the parsed
/// [`ViewNode`] — ready for [`CardPane::new`].
///
/// SpiderMonkey's engine is a process-global, thread-bound singleton, so `rt` is passed
/// in (the caller boots it once for the whole bake).
pub fn build_card_over_live(
    rt: &mut deos_js::JsRuntime,
    applet: AttachedApplet,
    applet_js: &str,
) -> Result<(AttachedApplet, ViewNode), String> {
    let outcome = rt
        .run_attached(applet, applet_js)
        .map_err(|e| format!("card view-tree authoring on the live World: {e}"))?;
    // The authoring JS stashes the stringified tree into the attached applet's ephemeral
    // view-state (NO turn) — and must commit no fires.
    if outcome.fires_committed != 0 {
        return Err(format!(
            "card view-tree authoring committed {} turn(s) — it must only build data",
            outcome.fires_committed
        ));
    }
    let attached = outcome.applet;
    let key = deos_view::view_tree_key();
    let json = attached
        .get_view(key)
        .ok_or_else(|| format!("card JS did not stash a view-tree under view-state '{key}'"))?
        .to_string();
    let tree = parse_view_tree(&json)?;
    Ok((attached, tree))
}

/// The ephemeral view-state key the card's authoring JS stashes its stringified
/// view-tree under (the SAME key [`build_card_over_live`] reads it back from). Exposed
/// so a bake's JS can name it consistently without depending on `deos-view` directly.
pub fn view_tree_key_for_card() -> &'static str {
    deos_view::view_tree_key()
}

/// A stable id salt for a button from its label (so two buttons in one card differ).
fn label_hash(label: &str) -> u64 {
    let mut h: u64 = 1469598103934665603; // FNV-1a offset
    for b in label.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(1099511628211);
    }
    h
}
