//! THE GUEST / APP-FORWARD FRONT DOOR — the welcoming desktop a newcomer lands on.
//!
//! Real first-user feedback (spwashi): "the screenshot feels verbose." They met
//! the *adept's inspector* (the dense RawFields/Graph/Provenance faces — a wall of
//! hashes) when what a guest wants is the *apps*. This module is the fix: the
//! **app-forward-by-default** desktop, the "after you dismiss the inspector" view.
//!
//! ember's framing: *"dismiss the inspector and find yourself with a browser, zed,
//! a terminal, a chat program, and a rolodex of gizmos and gadgets acquired from
//! the journey through the multi-user dungeon called deos."* That is exactly the
//! composition here:
//!
//!   * the **app surfaces** — a web-shell/browser tile, the [`EditorPane`] (deos-
//!     zed), the [`TerminalPane`] (deos-terminal), and the [`ChatPane`] (deos-
//!     matrix) — the real surfaces the cockpit mounts, here laid out clean as a
//!     guest's desktop, NOT buried under inspector chrome;
//!   * a **launcher-rolodex** of gadgets — one card per wired
//!     [`AppRegistry`](crate::app_registry::AppRegistry) entry (gallery · auction ·
//!     bounty · tussle · …), PARTITIONED by the live session c-list: a gadget is
//!     *acquired* iff the session actually holds its cap ([`Session::reaches`] —
//!     the MUD's "you picked it up = you hold the cap"); the rest of the catalog
//!     renders discoverable-but-not-held (dimmed), never silently equal;
//!   * a **wonder strip** — a few glowing, pokeable cells (the AOL register, glow =
//!     recent activity) drawn from the live [`WonderRoom`](crate::wonder::WonderRoom);
//!   * and the inspector is **NOT shown** — it is one summon away (the ⌘K /
//!     *inspect* affordance in the top bar). The adept's power is preserved; it is
//!     *summoned, not default*.
//!
//! ## The design (`docs/deos/SCRIPTING-AND-DISTRIBUTED-DOM.md §7`)
//!
//! Every cell has 7 `obs`-faces; the app's *pretty* view is the `DomainVisual`
//! face, the inspector is the RawFields/Graph/Provenance faces. A guest lands on
//! the app/DomainVisual faces; the inspector is one **halo** (⌘K / a summon) away —
//! the SAME objects, a different default. This module composes the DomainVisual
//! default; the cockpit's existing inspector surfaces (`cell_inspector`, `graph`,
//! `proofs`) are the summoned faces, unchanged.
//!
//! Like [`crate::showcase`], the surfaces are REAL (no surface mockups — the actual
//! deos-zed / deos-terminal / deos-matrix code), seeded deterministically, rendered
//! offscreen via the same gpui headless path the cockpit bake uses. The rolodex +
//! wonder strip are read off the real [`AppRegistry`] + the live `demo_world` image.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use gpui::prelude::FluentBuilder;
use gpui::{
    div, px, App, AppContext, Context, Entity, FocusHandle, Focusable, InteractiveElement,
    IntoElement, KeyDownEvent, ParentElement, Render, Styled, Window,
};

use dregg_cell::CellId;

use crate::app_registry::AppRegistry;
use crate::dock::chat_surface::ChatPane;
use crate::dock::editor_surface::EditorPane;
use crate::dock::surface::CockpitSurface;
use crate::dock::terminal_surface::TerminalPane;
use crate::session::Session;
use crate::wonder::WonderRoom;
use crate::world::World;

/// The guest palette — a self-contained mirror of the dock's GitHub-dark values
/// (the dock's `theme` module is private to the dock; this keeps the guest view
/// from reaching into a sibling-owned module, exactly as `showcase` does).
mod theme {
    use gpui::{rgb, Hsla};
    pub fn bg() -> Hsla {
        rgb(0x0e1116).into()
    }
    pub fn panel() -> Hsla {
        rgb(0x161b22).into()
    }
    pub fn panel_hi() -> Hsla {
        rgb(0x1f2630).into()
    }
    pub fn border() -> Hsla {
        rgb(0x2b3340).into()
    }
    pub fn text() -> Hsla {
        rgb(0xd7dee8).into()
    }
    pub fn muted() -> Hsla {
        rgb(0x7d8794).into()
    }
    pub fn accent() -> Hsla {
        rgb(0x6cb6ff).into()
    }
}

fn rgb_ok() -> gpui::Hsla {
    gpui::rgb(0x57d97f).into()
}

/// Whether a rolodex gadget is actually POSSESSED — the MUD's "you picked it up =
/// you hold the cap". Decided by the live session c-list ([`Session::reaches`]),
/// never by the registry: the registry is the catalog, the c-list is possession.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Possession {
    /// The session's c-list reaches this gadget's app cell — acquired, held.
    Held,
    /// A catalog entry whose cap the session does NOT hold (or there is no
    /// session / no launched cell to hold) — discoverable, rendered dimmed,
    /// never silently equal to a held gadget.
    Discoverable,
}

/// One **gadget** in the launcher-rolodex — a wired app from the real
/// [`crate::app_registry::AppEntry`] catalog. Pure data (the glyph + the entry's
/// real name/description + its [`Possession`]), so the rolodex content is read off
/// the live registry AND the live session c-list, never a mock list.
struct Gadget {
    glyph: &'static str,
    name: String,
    blurb: String,
    /// Is the gadget's cap actually held by the session (the c-list decides)?
    possession: Possession,
}

impl Gadget {
    fn held(&self) -> bool {
        self.possession == Possession::Held
    }
}

/// The gadget rolodex, partitioned by POSSESSION — one card per wired registry
/// entry, in registry order, each marked [`Possession::Held`] iff the live
/// `session` actually REACHES the gadget's app cell in the ledger
/// ([`Session::reaches`] — the same c-list read the WM makes). The MUD semantics:
/// picking a gadget up moved its cap into your c-list (`mud::pick_up`), so
/// "acquired" is a fact of the ledger, not of the catalog.
///
/// `gadget_cells` is the id → app-cell designation of the gadgets that EXIST in
/// this world (a launched app's cell, e.g. `LaunchedOnWorld::primary_cell()`,
/// keyed by registry id). A registry [`crate::app_registry::AppEntry`] carries
/// `{id, name, description, backend}` and NO `CellId` — a gadget's cap identity
/// is born at launch, exactly as a MUD item is a cell in the world, so the host
/// that launched the apps supplies the designations. An entry with no session, no
/// designated cell, or an unreached cell is [`Possession::Discoverable`] — the
/// catalog face, honestly not-held.
fn acquired_gadgets(
    session: Option<(&Session, &World)>,
    gadget_cells: &[(&str, CellId)],
) -> Vec<Gadget> {
    AppRegistry::standard()
        .entries()
        .iter()
        .map(|e| {
            let cell = gadget_cells
                .iter()
                .find(|(id, _)| *id == e.id)
                .map(|(_, c)| *c);
            let held = match (session, cell) {
                (Some((s, w)), Some(c)) => s.reaches(w, &c),
                _ => false,
            };
            Gadget {
                glyph: glyph_for(e.id),
                name: e.name.to_string(),
                blurb: e.description.to_string(),
                possession: if held {
                    Possession::Held
                } else {
                    Possession::Discoverable
                },
            }
        })
        .collect()
}

/// Project the live image's cells into the dense inspector rows — the SAME
/// `reflect::reflect_cell` the OBJECTS/inspector tab shows. This is the adept's
/// "wall of hashes" face, built here so the F11 summon is an instant show of real
/// reflective data over the same objects the apps present prettily.
fn reflected_rows(world: &World) -> Vec<InspectorRow> {
    let mut cells: Vec<_> = world.ledger().iter().collect();
    cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    cells
        .into_iter()
        .map(|(id, cell)| {
            let obj = crate::reflect::reflect_cell(id, cell);
            let fields = obj
                .fields
                .iter()
                .map(|f| format!("{} = {}", f.key, field_display(&f.value)))
                .collect();
            InspectorRow {
                title: obj.title,
                subtitle: obj.subtitle,
                fields,
            }
        })
        .collect()
}

/// Render a reflective field value as the dense inspector text (hashes/ids in
/// short-hex, the raw verbose face).
fn field_display(v: &crate::reflect::FieldValue) -> String {
    use crate::reflect::FieldValue;
    match v {
        FieldValue::Text(s) => s.clone(),
        FieldValue::Balance(b) => format!("{b}"),
        FieldValue::Count(c) => format!("{c}"),
        FieldValue::Bool(b) => format!("{b}"),
        FieldValue::Id(bytes) | FieldValue::Hash(bytes) => crate::reflect::short_hex(bytes),
        FieldValue::CapEdge { target, slot } => {
            format!("→ {} @slot {slot}", crate::reflect::short_hex(target))
        }
        FieldValue::FieldSlot { index, hex } => format!("[{index}] {hex}"),
    }
}

/// A warm glyph for a known registry id (the wonder register: a child reads the
/// glyph, an adept reads the name). Falls back to a generic gadget mark.
fn glyph_for(id: &str) -> &'static str {
    match id {
        "gallery" => "🖼",
        "sealed-auction" => "🔨",
        "bounty-board" => "📌",
        "tussle" => "🥊",
        "agent-orchestration" => "🧭",
        "agent-provenance" => "🔗",
        "compartment-workflow-mandate" => "📋",
        "compute-exchange" => "⚙",
        "escrow-market" => "🤝",
        "nameservice" => "🏷",
        "privacy-voting" => "🗳",
        "storage-gateway-mandate" => "🗄",
        _ => "✦",
    }
}

/// The guest desktop root view — owns the seeded app surfaces + the acquired-gadget
/// rolodex + the wonder strip, and lays them out app-forward (the inspector is NOT
/// mounted; it is summonable from the top bar).
pub struct GuestView {
    browser_url: String,
    editor: EditorPane,
    terminal: TerminalPane,
    chat: ChatPane,
    gadgets: Vec<Gadget>,
    /// The wonder strip — a handful of the brightest glowing cells (glow = recent
    /// activity), the AOL-pokeable register read off the live image.
    glow: Vec<(String, f32)>,
    /// THE SUMMONED INSPECTOR FACE — the dense RawFields projection of the live
    /// cells (the SAME objects, the adept's verbose face), precomputed off the
    /// real `reflect::reflect_cell`. Shown ONLY when [`Self::inspector_summoned`] is
    /// true (the F11/⌘K summon); the app-forward default never renders it.
    inspector_rows: Vec<InspectorRow>,
    /// Is the inspector overlay currently summoned? `false` by default (app-forward,
    /// even for the owner — the inspector is summoned, never the default). Flipped by
    /// the real F11 / ⌘K keystroke handler ([`Self::toggle_inspector`]).
    inspector_summoned: bool,
    focus: FocusHandle,
}

/// One titled object in the summoned inspector overlay — a cell's reflective title
/// + its dense field lines (the "wall of hashes" face, on purpose, on summon only).
struct InspectorRow {
    title: String,
    subtitle: String,
    fields: Vec<String>,
}

impl GuestView {
    /// Build the guest desktop over the seeded demo image. The app surfaces are
    /// constructed through their real surface code (exactly as `showcase` does); the
    /// rolodex + wonder strip are read off the real registry + the live ledger.
    pub fn build(world: Rc<RefCell<World>>, window: &mut Window, cx: &mut App) -> Self {
        // EDITOR — a seeded in-memory document (real, highlighted Rust + on-ledger
        // patch history). File tree roots at the real repo so the left rail is live.
        let repo_root = std::env::current_dir()
            .ok()
            .and_then(|d| d.parent().map(|p| p.to_path_buf()))
            .unwrap_or_else(|| std::path::PathBuf::from("."));
        let editor = EditorPane::seeded(
            2,
            deos_zed::fs::RealFs::arc(),
            repo_root,
            "welcome.rs",
            &GUEST_EDITOR_REVISIONS,
            window,
            cx,
        );

        // TERMINAL — a recorded, friendly shell session (deterministic, no live PTY).
        let terminal = TerminalPane::seeded(3, 80, 18, GUEST_TERMINAL_SESSION.as_bytes(), cx);

        // CHAT — fully REAL, no mock anywhere. The TRANSPORT is the dregg world
        // itself (`WorldChatSource`): rooms are real cells, a sent message is a real
        // verified turn, the timeline is read back from real cell state. The MEMBRANE
        // affordances are REAL too: the comms-PD source wraps the world-chat and
        // snapshots a fork of the SAME chat world (the "screenshot a moment"),
        // rehydrating/driving/stitching genuine `Cell` frusta. Every button drives
        // the real executor — never a mock envelope, never a recorded sync.
        let world_chat = crate::world_chat::WorldChatSource::seeded("@ember:deos.local");
        let membrane_world = world_chat.fork_world();
        let focus = world_chat.me_cell();
        let transport: Arc<dyn deos_matrix::source::ChatSource> = Arc::new(world_chat);
        let source: Arc<dyn deos_matrix::source::ChatSource> = Arc::new(
            crate::comms_pd_source::CommsPdSource::new(transport, membrane_world, focus, 3),
        );
        let chat = ChatPane::new(4, source, window, cx);

        // The wonder strip — the brightest few glowing cells off the live image.
        let room = WonderRoom::build(&world.borrow());
        let mut glow: Vec<(String, f32)> = room
            .cells
            .iter()
            .map(|c| (crate::reflect::short_hex(c.cell.as_bytes()), c.liveliness))
            .collect();
        glow.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        glow.truncate(5);

        // Precompute the SUMMONED inspector face — the dense RawFields projection of
        // the live cells (the same `reflect::reflect_cell` the OBJECTS tab shows).
        // Built once here so the F11 summon is an instant show/hide of real data.
        let inspector_rows = reflected_rows(&world.borrow());

        Self {
            browser_url: "dregg://welcome".to_string(),
            editor,
            terminal,
            chat,
            // The guest bake mounts with NO logged-in session (and no launched
            // gadget cells), so every catalog entry renders honestly as
            // discoverable-not-held — possession is the c-list's to grant, never
            // implied by the catalog. A host with a live session partitions via
            // `acquired_gadgets(Some((&session, &world)), &launched_cells)`.
            gadgets: acquired_gadgets(None, &[]),
            glow,
            inspector_rows,
            // App-forward by DEFAULT — the inspector is summoned, never the default
            // (true even for the owner; F11 brings it up).
            inspector_summoned: false,
            focus: cx.focus_handle(),
        }
    }

    /// Is the dense inspector overlay currently summoned? Read by the bake to prove
    /// the default is app-forward (false) and that F11 flips it on.
    pub fn inspector_summoned(&self) -> bool {
        self.inspector_summoned
    }

    /// **The real summon toggle** — show/hide the inspector overlay. Bound to F11
    /// (and ⌘K), this is a genuine state flip the keystroke handler calls; the
    /// render reads the flag, so the overlay appears/disappears live.
    pub fn toggle_inspector(&mut self) {
        self.inspector_summoned = !self.inspector_summoned;
    }

    /// Drive the REAL key handler with a `KeyDownEvent` — the exact path the live
    /// `.on_key_down` listener calls (the listener forwards to `on_key`). The bake
    /// uses this to fire a synthesized F11 (a headless window has no physical
    /// keyboard) and prove the keybind flips the summon. NOT a separate code path:
    /// it runs the identical `on_key` the window's listener runs.
    pub fn dispatch_key(&mut self, ev: &KeyDownEvent, cx: &mut Context<Self>) {
        self.on_key(ev, cx);
    }

    /// The key handler — F11 (or ⌘K / Ctrl-K) toggles the inspector summon; Escape
    /// dismisses it. A real keystroke path (mirrors the cockpit's `on_key`), so the
    /// summon is live-interactive, not a stub.
    fn on_key(&mut self, ev: &KeyDownEvent, cx: &mut Context<Self>) {
        let ks = &ev.keystroke;
        let key = ks.key.as_str();
        let cmd = ks.modifiers.platform || ks.modifiers.control;
        if key == "f11" || (cmd && key == "k") {
            self.toggle_inspector();
            cx.notify();
        } else if key == "escape" && self.inspector_summoned {
            self.inspector_summoned = false;
            cx.notify();
        }
    }

    /// The top **welcome bar** — the warm greeting + the INSPECTOR SUMMON. The
    /// inspector is not shown; this bar is where a guest summons it (⌘K / *inspect*).
    /// The summon affordance is rendered prominently so the adept's power is one
    /// click away while the default stays clean.
    fn welcome_bar(&self) -> impl IntoElement {
        div()
            .flex()
            .items_center()
            .gap_3()
            .px_4()
            .py_2()
            .w_full()
            .bg(theme::panel())
            .border_b_1()
            .border_color(theme::border())
            .child(
                div()
                    .text_color(theme::accent())
                    .text_lg()
                    .font_weight(gpui::FontWeight::BOLD)
                    .child("◈ deos"),
            )
            .child(
                div()
                    .text_color(theme::text())
                    .text_sm()
                    .child("welcome — here are your apps"),
            )
            .child(div().flex_1())
            // THE INSPECTOR SUMMON — the one halo away. A guest stays app-forward;
            // pressing this (⌘K) opens the dense inspector faces over the SAME objects.
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .px_3()
                    .py_1()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .border_1()
                    .border_color(theme::accent())
                    .text_color(theme::accent())
                    .text_xs()
                    .child("⌘K")
                    .child(div().text_color(theme::muted()).child("summon inspector")),
            )
    }

    /// A titled app-window frame — a small header strip + the surface body, so each
    /// app reads as a distinct, labelled window (the same `framed` shape `showcase`
    /// uses, kept local so this lane owns its chrome).
    fn framed(title: &str, subtitle: &str, body: gpui::AnyElement) -> impl IntoElement {
        div()
            .flex()
            .flex_col()
            .flex_1()
            .min_h(px(0.))
            .overflow_hidden()
            .rounded_lg()
            .bg(theme::bg())
            .border_1()
            .border_color(theme::border())
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .px_3()
                    .py_1()
                    .bg(theme::panel())
                    .border_b_1()
                    .border_color(theme::border())
                    .child(
                        div()
                            .text_color(theme::text())
                            .text_xs()
                            .font_weight(gpui::FontWeight::SEMIBOLD)
                            .child(title.to_string()),
                    )
                    .child(
                        div()
                            .text_color(theme::muted())
                            .text_xs()
                            .child(subtitle.to_string()),
                    ),
            )
            .child(div().flex_1().min_h(px(0.)).overflow_hidden().child(body))
    }

    /// The **browser tile** — a clean web-shell card. A real Servo render is behind
    /// the `web-shell` feature + the net-cap gate (and needs a network); for the
    /// guest bake this is the surface's resting chrome: an address bar + a friendly
    /// landing page. (Honest: this tile is the browser CHROME, not a live page
    /// fetch — the real render lives in the cockpit's WEB-SHELL tab.)
    fn browser_body(&self) -> gpui::AnyElement {
        div()
            .flex()
            .flex_col()
            .size_full()
            .bg(theme::bg())
            .child(
                // The address bar.
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .px_2()
                    .py_1()
                    .bg(theme::panel())
                    .border_b_1()
                    .border_color(theme::border())
                    .child(div().text_color(theme::muted()).text_xs().child("◀ ▶ ⟳"))
                    .child(
                        div()
                            .flex_1()
                            .px_2()
                            .py_1()
                            .rounded_md()
                            .bg(theme::panel_hi())
                            .text_color(theme::text())
                            .text_xs()
                            .child(self.browser_url.clone()),
                    ),
            )
            .child(
                // The page body — a warm landing, no wall of hashes.
                div()
                    .flex()
                    .flex_col()
                    .gap_2()
                    .p_4()
                    .flex_1()
                    .child(
                        div()
                            .text_color(theme::accent())
                            .text_lg()
                            .font_weight(gpui::FontWeight::BOLD)
                            .child("you are inside deos"),
                    )
                    .child(div().text_color(theme::muted()).text_xs().child(
                        "a live, verified, object-capability world. click around — \
                                 every app here is a real surface over the same image.",
                    )),
            )
            .into_any_element()
    }

    /// The **launcher-rolodex** rail — one card per gadget, read off the live
    /// registry AND partitioned by the live session c-list: a HELD gadget (the
    /// session reaches its cap — the MUD's "you picked it up") renders bright; a
    /// DISCOVERABLE one (catalog only, cap not held) renders dimmed with a "not
    /// held" tag — never silently equal.
    fn rolodex(&self) -> impl IntoElement {
        let held_count = self.gadgets.iter().filter(|g| g.held()).count();
        let discoverable_count = self.gadgets.len() - held_count;
        let mut rail = div()
            .flex()
            .flex_col()
            .gap_2()
            .w(px(264.))
            .h_full()
            .p_3()
            .bg(theme::panel())
            .border_r_1()
            .border_color(theme::border())
            .child(
                div()
                    .flex()
                    .items_baseline()
                    .gap_2()
                    .child(
                        div()
                            .text_color(theme::text())
                            .text_sm()
                            .font_weight(gpui::FontWeight::SEMIBOLD)
                            .child("YOUR GADGETS"),
                    )
                    .child(div().text_color(theme::muted()).text_xs().child(format!(
                        "{held_count} held · {discoverable_count} discoverable"
                    ))),
            )
            .child(
                div()
                    .text_color(theme::muted())
                    .text_xs()
                    .child("the rolodex — held = the cap is in your c-list · dimmed = not held"),
            );

        for g in &self.gadgets {
            let held = g.held();
            // Possession decides the card's face: a held gadget is bright; a
            // discoverable one is dimmed (glyph + name muted) and tagged.
            let (glyph_color, name_color) = if held {
                (theme::accent(), theme::text())
            } else {
                (theme::muted(), theme::muted())
            };
            let mut title_row = div().flex().items_baseline().gap_1().child(
                div()
                    .text_color(name_color)
                    .text_xs()
                    .font_weight(gpui::FontWeight::SEMIBOLD)
                    .child(g.name.clone()),
            );
            if !held {
                title_row = title_row.child(
                    div()
                        .text_color(theme::muted())
                        .text_xs()
                        .child("· not held"),
                );
            }
            rail = rail.child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .border_1()
                    .border_color(theme::border())
                    .when(!held, |card| card.opacity(0.6))
                    .child(div().text_color(glyph_color).text_sm().child(g.glyph))
                    .child(
                        div()
                            .flex()
                            .flex_col()
                            .flex_1()
                            .min_w(px(0.))
                            .overflow_hidden()
                            .child(title_row)
                            .child(
                                div()
                                    .text_color(theme::muted())
                                    .text_xs()
                                    .overflow_hidden()
                                    .child(truncate(&g.blurb, 64)),
                            ),
                    ),
            );
        }

        rail.child(div().flex_1())
    }

    /// The bottom **wonder strip** — a few glowing pokeable cells (glow = recent
    /// activity), the AOL-wonder register read off the live image. Welcoming and
    /// low-verbosity: just bright dots a guest can poke, not a field dump.
    fn wonder_strip(&self) -> impl IntoElement {
        let mut row = div()
            .flex()
            .items_center()
            .gap_3()
            .w_full()
            .px_4()
            .py_2()
            .bg(theme::panel())
            .border_t_1()
            .border_color(theme::border())
            .child(
                div()
                    .text_color(theme::muted())
                    .text_xs()
                    .child("✦ live cells — poke one:"),
            );
        for (label, liveliness) in &self.glow {
            // Glow → a brighter dot for a more-recently-touched cell.
            let dot = if *liveliness > 0.66 {
                rgb_ok()
            } else if *liveliness > 0.0 {
                theme::accent()
            } else {
                theme::muted()
            };
            row = row.child(
                div()
                    .flex()
                    .items_center()
                    .gap_1()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .child(div().text_color(dot).text_xs().child("●"))
                    .child(
                        div()
                            .text_color(theme::muted())
                            .text_xs()
                            .child(label.clone()),
                    ),
            );
        }
        row.child(div().flex_1()).child(
            div()
                .text_color(theme::muted())
                .text_xs()
                .child("brighter = the image just touched it"),
        )
    }

    /// THE SUMMONED INSPECTOR OVERLAY — the dense RawFields face of the live cells,
    /// rendered ONLY when [`Self::inspector_summoned`] is true (the F11/⌘K summon).
    /// This is deliberately the "verbose" view (titles + a wall of fields/hashes) —
    /// the adept's power — over the SAME objects the apps present prettily. It is an
    /// overlay, so dismissing it (F11/Escape) returns to the clean app-forward view.
    fn inspector_overlay(&self) -> impl IntoElement {
        // A right-docked panel (not a full takeover) — the apps stay visible behind
        // it, reinforcing "same objects, summoned face".
        let mut panel = div()
            .flex()
            .flex_col()
            .gap_3()
            .w(px(420.))
            .h_full()
            .p_4()
            .bg(theme::panel())
            .border_l_1()
            .border_color(theme::accent())
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .child(
                        div()
                            .text_color(theme::accent())
                            .text_sm()
                            .font_weight(gpui::FontWeight::BOLD)
                            .child("⚙ inspector"),
                    )
                    .child(div().flex_1())
                    .child(
                        div()
                            .text_color(theme::muted())
                            .text_xs()
                            .child("F11 / Esc to dismiss"),
                    ),
            )
            .child(div().text_color(theme::muted()).text_xs().child(format!(
                "{} live cells · the same objects, the raw face",
                self.inspector_rows.len()
            )));

        for row in &self.inspector_rows {
            let mut card = div()
                .flex()
                .flex_col()
                .gap_1()
                .p_2()
                .rounded_md()
                .bg(theme::panel_hi())
                .border_1()
                .border_color(theme::border())
                .child(
                    div()
                        .text_color(theme::text())
                        .text_xs()
                        .font_weight(gpui::FontWeight::SEMIBOLD)
                        .child(row.title.clone()),
                )
                .child(
                    div()
                        .text_color(theme::muted())
                        .text_xs()
                        .child(row.subtitle.clone()),
                );
            for f in &row.fields {
                card = card.child(
                    div()
                        .text_color(theme::muted())
                        .text_xs()
                        .font_family("Menlo")
                        .child(f.clone()),
                );
            }
            panel = panel.child(card);
        }

        // The dim scrim behind the panel + the right-docked panel itself.
        div()
            .absolute()
            .inset_0()
            .flex()
            .justify_end()
            .bg(gpui::rgba(0x0e111688))
            .child(panel)
    }
}

impl Focusable for GuestView {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for GuestView {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let editor_body = self.editor.render_body(window, cx);
        let terminal_body = self.terminal.render_body(window, cx);
        let chat_body = self.chat.render_body(window, cx);
        let browser_body = self.browser_body();

        // LEFT COLUMN: the browser (top) above the editor — the "look around / make
        // something" half of the desktop.
        let left_column = div()
            .flex()
            .flex_col()
            .gap_3()
            .flex_1()
            .min_w(px(0.))
            .h_full()
            .child(Self::framed(
                "browser · web-shell",
                "http(s):// over the net-cap gate",
                browser_body,
            ))
            .child(Self::framed(
                "editor · deos-zed",
                "syntax-highlit · on-ledger patches",
                editor_body,
            ));

        // RIGHT COLUMN: chat (top) above the terminal — the "talk / do" half.
        let right_column = div()
            .flex()
            .flex_col()
            .gap_3()
            .flex_1()
            .min_w(px(0.))
            .h_full()
            .child(Self::framed(
                "chat · deos-matrix",
                "rooms · the chat IS the dregg world",
                chat_body,
            ))
            .child(Self::framed(
                "terminal · deos-terminal",
                "a friendly shell",
                terminal_body,
            ));

        let summoned = self.inspector_summoned;
        div()
            .id("guest-root")
            .key_context("Guest")
            .track_focus(&self.focus)
            // F11 / ⌘K summon the inspector (a REAL keystroke handler) — Escape dismisses.
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
            .child(self.welcome_bar())
            .child(
                div()
                    .flex()
                    .flex_1()
                    .min_h(px(0.))
                    .w_full()
                    .child(self.rolodex())
                    .child(
                        div()
                            .flex()
                            // HIG: generous gutters + breathing room between the app
                            // windows (restraint, not a dense dev-tool wall).
                            .gap_4()
                            .flex_1()
                            .min_w(px(0.))
                            .h_full()
                            .p_4()
                            .child(left_column)
                            .child(right_column),
                    ),
            )
            .child(self.wonder_strip())
            // THE SUMMONED INSPECTOR — rendered ONLY when summoned (F11/⌘K). The
            // app-forward default has ZERO inspector chrome, even for the owner.
            .when(summoned, |root| root.child(self.inspector_overlay()))
    }
}

/// Mount the guest desktop as a root view for the headless capture.
pub fn build_root(
    world: Rc<RefCell<World>>,
    window: &mut Window,
    cx: &mut App,
) -> Entity<GuestView> {
    let view = cx.new(|cx| GuestView::build(world, window, cx));
    view.update(cx, |v, cx| {
        let focus = v.focus.clone();
        focus.focus(window, cx);
    });
    view
}

/// Truncate a blurb to `max` chars with an ellipsis, so a long app description does
/// not overflow the narrow rolodex card.
fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        return s.to_string();
    }
    let mut out: String = s.chars().take(max.saturating_sub(1)).collect();
    out.push('…');
    out
}

/// The seeded editor document — a warm, welcoming Rust slice (the guest's first
/// file), with a small on-ledger revision history so the patch count is real.
const GUEST_EDITOR_REVISIONS: [&str; 2] = [
    "//! welcome.rs — your first file in deos.\n\nfn main() {\n    println!(\"hello from inside the verified image\");\n}\n",
    "//! welcome.rs — your first file in deos.\n//! every save here is a real, receipted turn on the live ledger.\n\nfn main() {\n    // poke around. open an app from the rolodex. press ⌘K for the inspector.\n    println!(\"hello from inside the verified image\");\n}\n",
];

/// The recorded terminal session — a friendly, low-noise shell (no wall of build
/// output), fed straight into the grid. `\r\n` line breaks (terminal convention).
const GUEST_TERMINAL_SESSION: &str = concat!(
    "\x1b[32mguest@deos\x1b[0m:\x1b[34m~\x1b[0m$ ls\r\n",
    "welcome.rs   apps/   journal.txt\r\n",
    "\x1b[32mguest@deos\x1b[0m:\x1b[34m~\x1b[0m$ deos apps\r\n",
    "  gallery   auction   bounty   tussle   …  (open one from the rolodex)\r\n",
    "\x1b[32mguest@deos\x1b[0m:\x1b[34m~\x1b[0m$ \x1b[5m▋\x1b[0m\r\n",
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session::{CapEntry, CapTemplate, LoginManager, LoginOutcome};
    use crate::world::make_open_cell;
    use dregg_cell::AuthRequired;

    #[test]
    fn the_rolodex_is_read_off_the_real_registry() {
        // The rolodex is EXACTLY the wired registry entries (one card per app), in
        // registry order — a live projection, never a mock list. With NO session,
        // every entry is honestly DISCOVERABLE: the catalog never implies possession.
        let gadgets = acquired_gadgets(None, &[]);
        let entries = AppRegistry::standard();
        assert_eq!(
            gadgets.len(),
            entries.entries().len(),
            "one gadget card per wired registry app"
        );
        assert!(
            !gadgets.is_empty(),
            "the catalog offers at least one gadget"
        );
        // Each gadget carries the registry entry's REAL name + a non-empty blurb,
        // and with no session NONE reads as held.
        for (g, e) in gadgets.iter().zip(entries.entries().iter()) {
            assert_eq!(g.name, e.name, "the card shows the app's real name");
            assert!(
                !g.blurb.trim().is_empty(),
                "the card shows a real description"
            );
            assert!(!g.glyph.is_empty(), "the card carries a warm glyph");
            assert_eq!(
                g.possession,
                Possession::Discoverable,
                "no session → no possession: the catalog is not the c-list"
            );
        }
        // Known apps get warm glyphs (the wonder register), not the fallback mark.
        assert!(
            gadgets
                .iter()
                .any(|g| g.name == "Sealed Gallery" && g.glyph == "🖼"),
            "the gallery gadget gets its warm glyph"
        );
    }

    /// A world with a launched gallery gadget cell + a system principal holding
    /// full authority over it (the ceiling a session template attenuates from) —
    /// the login fixture for the possession tests. Returns
    /// `(world, manager, gallery_cell)`.
    fn gadget_world() -> (World, LoginManager, CellId) {
        let mut w = World::new();
        // The gadget's app cell — the cap identity a launched gallery would have
        // on this world (a MUD item is a cell in the world).
        let gallery_cell = w.genesis_cell(0xA0, 0);
        // The system principal holds the gadget cap — what login grants FROM.
        let mut sys = make_open_cell(0x55, 0);
        sys.capabilities
            .grant(gallery_cell, AuthRequired::None)
            .expect("the system principal holds the gadget cap");
        let system_principal = w.genesis_install(sys);
        (w, LoginManager::new(system_principal), gallery_cell)
    }

    /// THE MUD TOOTH, positive face: a session that HOLDS a gadget's cap (granted
    /// through the REAL login ceremony — a real `Effect::GrantCapability` turn)
    /// sees that gadget as ACQUIRED, and only that gadget: possession is per-cap,
    /// read off the live c-list, never a blanket flag.
    #[test]
    fn a_session_holding_the_gadget_cap_sees_it_acquired() {
        let (mut w, mgr, gallery_cell) = gadget_world();
        let p = mgr.authenticate([7u8; 32], true).expect("auth passes");
        // The template grants the gallery gadget cap into the session root — the
        // "you picked it up" moment, via the real grant path.
        let template = CapTemplate::empty().with(CapEntry::new(
            gallery_cell,
            AuthRequired::None,
            true,
            "gallery gadget",
        ));
        let session = match mgr.login(&mut w, p, &template) {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("login should succeed: {reason}"),
        };
        // The live c-list really reaches the gadget cell (the same read the WM makes).
        assert!(
            session.reaches(&w, &gallery_cell),
            "the ceremony granted the gadget cap"
        );

        let gadgets = acquired_gadgets(Some((&session, &w)), &[("gallery", gallery_cell)]);
        let gallery = gadgets
            .iter()
            .find(|g| g.name == "Sealed Gallery")
            .expect("the gallery is in the catalog");
        assert_eq!(
            gallery.possession,
            Possession::Held,
            "the session holds the gallery cap → the gadget is ACQUIRED"
        );
        // Every OTHER catalog entry stays discoverable — possession is per-cap.
        for g in gadgets.iter().filter(|g| g.name != "Sealed Gallery") {
            assert_eq!(
                g.possession,
                Possession::Discoverable,
                "{} has no held cap — it must not read as acquired",
                g.name
            );
        }
        assert_eq!(
            gadgets.iter().filter(|g| g.held()).count(),
            1,
            "exactly the one held cap partitions as acquired"
        );
    }

    /// THE MUD TOOTH, negative face: a session WITHOUT the gadget's cap (an empty
    /// template — the ocap floor) sees the gadget as NOT acquired, even though the
    /// gadget cell exists in the world and is designated. The registry stays the
    /// catalog; the c-list decides possession.
    #[test]
    fn a_session_without_the_cap_sees_it_not_acquired() {
        let (mut w, mgr, gallery_cell) = gadget_world();
        let p = mgr.authenticate([9u8; 32], true).expect("auth passes");
        // Born holding NOTHING — the ocap floor.
        let session = match mgr.login(&mut w, p, &CapTemplate::empty()) {
            LoginOutcome::Session(s) => s,
            LoginOutcome::Denied { reason } => panic!("login should succeed: {reason}"),
        };
        assert!(
            !session.reaches(&w, &gallery_cell),
            "the empty-template session holds no gadget cap"
        );

        let gadgets = acquired_gadgets(Some((&session, &w)), &[("gallery", gallery_cell)]);
        assert!(
            gadgets.iter().all(|g| !g.held()),
            "no held cap anywhere → NOTHING reads as acquired (never silently equal)"
        );
        let gallery = gadgets
            .iter()
            .find(|g| g.name == "Sealed Gallery")
            .expect("the gallery is in the catalog");
        assert_eq!(
            gallery.possession,
            Possession::Discoverable,
            "the gadget exists + is designated, but the cap is not held → discoverable only"
        );
    }

    #[test]
    fn truncate_keeps_short_blurbs_and_caps_long_ones() {
        assert_eq!(truncate("short", 64), "short");
        let long = "x".repeat(100);
        let t = truncate(&long, 10);
        assert_eq!(
            t.chars().count(),
            10,
            "a long blurb is capped to the card width"
        );
        assert!(t.ends_with('…'), "a capped blurb ends with an ellipsis");
    }

    #[test]
    fn glyph_for_known_ids_is_warm_and_unknown_falls_back() {
        assert_eq!(glyph_for("gallery"), "🖼");
        assert_eq!(glyph_for("tussle"), "🥊");
        assert_eq!(
            glyph_for("a-brand-new-app-id"),
            "✦",
            "unknown ids get the generic gadget mark"
        );
    }
}
