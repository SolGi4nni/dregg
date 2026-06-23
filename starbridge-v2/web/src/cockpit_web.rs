//! THE GPUI COCKPIT, IN THE BROWSER (first slice).
//!
//! This is NOT the JSON/atlas skin (`lib.rs`). This boots the REAL gpui
//! element-tree renderer — the same `gpui` the native cockpit draws with —
//! on the `gpui_web` backend (wasm32 + WebGPU canvas, via `gpui_platform`'s
//! wasm forwarding). The view here renders a live slice of the cockpit (the
//! HOME cell-roster + a cell INSPECTOR) over the SAME embedded executor
//! (`starbridge_v2::world::World`) the native cockpit drives.
//!
//! The point of this slice: prove gpui renders to an `HtmlCanvasElement` in
//! the browser, driving the in-browser verified `World` — one renderer, web
//! platform. The full `cockpit::Cockpit` (28 surfaces, dock, gpui-component
//! widgets) is the parity target; see docs/deos/WEB-DEOS.md for the distance.
//!
//! Boot path (identical in shape to native `run_window`, only the platform
//! differs): `gpui_platform::single_threaded_web()` → `.run(|cx| { … open a
//! window → `cx.new(CockpitWeb::new)` })`. On wasm `open_window` creates the
//! canvas and appends it to the document body; the WgpuRenderer paints the
//! resolved gpui `Scene` to it via WebGPU.

#![cfg(all(target_arch = "wasm32", feature = "gpui-web"))]

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, prelude::*, px, rgb, App, Context, FocusHandle, IntoElement, MouseButton, ParentElement,
    Render, SharedString, Styled, Window,
};
use wasm_bindgen::prelude::*;

use dregg_cell::permissions::AuthRequired;
use dregg_cell::CellId;
use starbridge_v2::inspect_act::{InspectAct, InspectFocus, SendResult};
use starbridge_v2::reflect::{self, FieldValue};
use starbridge_v2::world::{self, World};

// --- palette (the cockpit's dark surface, matching cockpit.html) ------------
const BG: u32 = 0x0d1117;
const BG2: u32 = 0x161b22;
const BG3: u32 = 0x0a0e14;
const LINE: u32 = 0x21262d;
const FG: u32 = 0xc9d1d9;
const MUTED: u32 = 0x8b949e;
const ACCENT: u32 = 0x58a6ff;
const GREEN: u32 = 0x3fb950;
const ORANGE: u32 = 0xf0883e;
const RED: u32 = 0xf85149;

/// One row in the live action log (a real turn through the executor).
struct LogLine {
    ok: bool,
    text: SharedString,
}

/// THE COCKPIT-SLICE VIEW — a real gpui `Render` entity over the live `World`.
/// Three columns (cells · inspector · affordances), mirroring the native
/// cockpit's left rail / center inspector / right action pane, driving the
/// same embedded executor. Clicks fire REAL cap-gated turns.
pub struct CockpitWeb {
    world: Rc<RefCell<World>>,
    anchors: [CellId; 3],
    selected: Option<CellId>,
    log: Vec<LogLine>,
    _focus: FocusHandle,
}

impl CockpitWeb {
    pub fn new(world: Rc<RefCell<World>>, anchors: [CellId; 3], cx: &mut Context<Self>) -> Self {
        Self {
            world,
            anchors,
            selected: Some(anchors[2]), // the user cell
            log: Vec::new(),
            _focus: cx.focus_handle(),
        }
    }

    fn select(&mut self, id: CellId, cx: &mut Context<Self>) {
        self.selected = Some(id);
        cx.notify();
    }

    /// Fire a message — a real cap-gated turn through the verified executor.
    fn act(&mut self, id: CellId, message: &str, cx: &mut Context<Self>) {
        let mut w = self.world.borrow_mut();
        let ia = InspectAct::build(&w, InspectFocus::Cell(id), id, AuthRequired::Either);
        let line = match ia.send(&mut w, message, AuthRequired::Either) {
            SendResult::Committed { receipt, .. } => LogLine {
                ok: true,
                text: format!(
                    "✓ {message} — {} computrons, {} actions",
                    receipt.computrons_used, receipt.action_count
                )
                .into(),
            },
            SendResult::Refused { reason, .. } => LogLine {
                ok: false,
                text: format!("✗ {message} — {reason}").into(),
            },
        };
        drop(w);
        self.log.insert(0, line);
        self.log.truncate(12);
        cx.notify();
    }
}

fn short(b: &[u8; 32]) -> String {
    let h = hex::encode(b);
    format!("{}…{}", &h[..6], &h[h.len() - 4..])
}

impl Render for CockpitWeb {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        // --- LEFT RAIL: the cell roster (HOME survey) -----------------------
        let world = self.world.borrow();
        let mut cell_rows = Vec::new();
        for (id, cell) in world.ledger().iter() {
            let id = *id;
            let insp = reflect::reflect_cell(&id, cell);
            let mut balance = None;
            for f in &insp.fields {
                if let ("balance", FieldValue::Balance(b)) = (&f.key[..], &f.value) {
                    balance = Some(*b);
                }
            }
            let is_sel = self.selected == Some(id);
            cell_rows.push(
                div()
                    .id(SharedString::from(hex::encode(id.as_bytes())))
                    .p(px(8.))
                    .mb(px(6.))
                    .rounded(px(7.))
                    .border_1()
                    .border_color(rgb(if is_sel { ORANGE } else { LINE }))
                    .bg(rgb(if is_sel { 0x1c2128 } else { BG2 }))
                    .cursor_pointer()
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _, _, cx| this.select(id, cx)),
                    )
                    .child(
                        div()
                            .text_color(rgb(ACCENT))
                            .child(SharedString::from(insp.title.clone())),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(rgb(MUTED))
                            .child(SharedString::from(short(id.as_bytes()))),
                    )
                    .when_some(balance, |el, b| {
                        el.child(
                            div()
                                .text_xs()
                                .text_color(rgb(ORANGE))
                                .child(SharedString::from(format!("balance {b}"))),
                        )
                    }),
            );
        }

        // --- CENTER: the inspector (the selected cell's faces) --------------
        let inspector: gpui::AnyElement = match self.selected {
            Some(id) => {
                if let Some(cell) = world.ledger().get(&id) {
                    let insp = reflect::reflect_cell(&id, cell);
                    let mut field_rows = Vec::new();
                    for f in &insp.fields {
                        field_rows.push(
                            div()
                                .flex()
                                .gap(px(8.))
                                .py(px(2.))
                                .child(
                                    div()
                                        .w(px(140.))
                                        .text_color(rgb(MUTED))
                                        .child(SharedString::from(f.key.clone())),
                                )
                                .child(
                                    div()
                                        .text_color(rgb(FG))
                                        .child(SharedString::from(fmt_field(&f.value))),
                                ),
                        );
                    }
                    div()
                        .child(
                            div()
                                .text_color(rgb(ACCENT))
                                .child(SharedString::from(insp.title.clone())),
                        )
                        .child(
                            div()
                                .text_xs()
                                .text_color(rgb(MUTED))
                                .mb(px(8.))
                                .child(SharedString::from(insp.subtitle.clone())),
                        )
                        .children(field_rows)
                        .into_any_element()
                } else {
                    div()
                        .text_color(rgb(MUTED))
                        .child("cell absent")
                        .into_any_element()
                }
            }
            None => div()
                .text_color(rgb(MUTED))
                .child("select a cell")
                .into_any_element(),
        };

        // --- RIGHT: affordances (the cap-gated messages) --------------------
        let mut msg_rows = Vec::new();
        if let Some(id) = self.selected {
            let ia = InspectAct::build(&world, InspectFocus::Cell(id), id, AuthRequired::Either);
            for m in &ia.messages {
                let name = m.name.clone();
                let authorized = m.authorized;
                let row = div()
                    .flex()
                    .justify_between()
                    .items_center()
                    .p(px(7.))
                    .mb(px(6.))
                    .rounded(px(7.))
                    .border_1()
                    .border_color(rgb(LINE))
                    .bg(rgb(BG2))
                    .child(
                        div()
                            .text_color(rgb(if authorized { FG } else { MUTED }))
                            .child(SharedString::from(m.name.clone())),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(rgb(if authorized { GREEN } else { RED }))
                            .child(if authorized { "send →" } else { "denied" }),
                    );
                let row = if authorized {
                    row.id(SharedString::from(name.clone()))
                        .cursor_pointer()
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _, _, cx| this.act(id, &name, cx)),
                        )
                } else {
                    row.id(SharedString::from(format!("no-{name}")))
                };
                msg_rows.push(row);
            }
        }

        // --- LOG (the real receipts) ----------------------------------------
        let mut log_rows = Vec::new();
        for l in &self.log {
            log_rows.push(
                div()
                    .text_xs()
                    .py(px(3.))
                    .text_color(rgb(if l.ok { GREEN } else { RED }))
                    .child(l.text.clone()),
            );
        }

        drop(world);

        let cell_count = self.world.borrow().ledger().iter().count();
        let _ = &self.anchors;

        // --- the cockpit shell ---------------------------------------------
        div()
            .size_full()
            .flex()
            .flex_col()
            .bg(rgb(BG))
            .text_color(rgb(FG))
            .font_family("Lilex")
            .text_sm()
            // header
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap(px(14.))
                    .p(px(12.))
                    .border_b_1()
                    .border_color(rgb(LINE))
                    .bg(rgb(BG3))
                    .child(
                        div()
                            .text_color(rgb(ACCENT))
                            .child("dregg · the verified ocap cockpit, live in your browser (gpui)"),
                    )
                    .child(
                        div()
                            .text_color(rgb(GREEN))
                            .text_xs()
                            .child(SharedString::from(format!("● {cell_count} cells · wasm"))),
                    ),
            )
            // body: three columns
            .child(
                div()
                    .flex_1()
                    .flex()
                    .min_h(px(0.))
                    .child(
                        // left rail
                        div()
                            .w(px(280.))
                            .p(px(12.))
                            .border_r_1()
                            .border_color(rgb(LINE))
                            .bg(rgb(BG3))
                            .child(div().text_color(rgb(ACCENT)).mb(px(8.)).child("cells"))
                            .children(cell_rows),
                    )
                    .child(
                        // center inspector
                        div()
                            .flex_1()
                            .p(px(12.))
                            .border_r_1()
                            .border_color(rgb(LINE))
                            .child(div().text_color(rgb(ACCENT)).mb(px(8.)).child("inspector"))
                            .child(inspector),
                    )
                    .child(
                        // right affordances + log
                        div()
                            .w(px(340.))
                            .p(px(12.))
                            .bg(rgb(BG3))
                            .child(
                                div()
                                    .text_color(rgb(ACCENT))
                                    .mb(px(8.))
                                    .child("affordances"),
                            )
                            .children(msg_rows)
                            .child(
                                div()
                                    .text_color(rgb(GREEN))
                                    .mt(px(16.))
                                    .mb(px(6.))
                                    .child("receipts"),
                            )
                            .children(log_rows),
                    ),
            )
    }
}

fn fmt_field(v: &FieldValue) -> String {
    match v {
        FieldValue::Text(s) => s.clone(),
        FieldValue::Balance(n) => format!("{n}"),
        FieldValue::Count(n) => format!("{n}"),
        FieldValue::Bool(b) => format!("{b}"),
        FieldValue::Id(id) => short(id),
        FieldValue::Hash(h) => short(h),
        FieldValue::CapEdge { target, slot } => format!("cap→{} [slot {slot}]", short(target)),
        FieldValue::FieldSlot { index, hex } => format!("slot {index}: {hex}"),
    }
}

/// THE WASM ENTRYPOINT — boot the gpui cockpit slice in the browser.
///
/// Called from JS (after `init()`): constructs a fresh seeded sovereign image
/// (`world::demo_world`, the same the native cockpit + atlas use), then boots a
/// single-threaded web gpui application, opens a window (which creates the
/// WebGPU canvas + appends it to the document body), and mounts the cockpit
/// slice view. The gpui run-loop drives paints/events thereafter.
#[wasm_bindgen]
pub fn boot_cockpit() {
    gpui_platform::web_init();

    let (world, anchors) = world::demo_world();
    let shared = Rc::new(RefCell::new(world));

    gpui_platform::single_threaded_web().run(move |cx: &mut App| {
        // Register the cockpit's font (the web platform bundles IBM Plex but not
        // Lilex; without it the Lilex-styled text falls back / blanks).
        static LILEX: &[u8] = include_bytes!("../../assets/fonts/Lilex-Regular.ttf");
        let _ = cx
            .text_system()
            .add_fonts(vec![std::borrow::Cow::Borrowed(LILEX)]);

        let bounds = gpui::Bounds {
            origin: gpui::point(px(0.), px(0.)),
            size: gpui::size(px(1280.), px(820.)),
        };
        cx.open_window(
            gpui::WindowOptions {
                window_bounds: Some(gpui::WindowBounds::Windowed(bounds)),
                ..Default::default()
            },
            move |_window, cx| cx.new(|cx| CockpitWeb::new(shared.clone(), anchors, cx)),
        )
        .expect("failed to open web window");
    });
}
