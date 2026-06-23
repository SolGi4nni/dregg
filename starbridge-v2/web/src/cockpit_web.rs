//! THE FULL GPUI COCKPIT, IN THE BROWSER — WITH THE EDITOR + CHAT PANES MOUNTED.
//!
//! This boots the REAL `starbridge_v2::cockpit::Cockpit` — the same comprehensive
//! master interface the native desktop opens — on the `gpui_web` backend (wasm32 +
//! WebGPU canvas, via `gpui_platform`'s wasm forwarding), driving the SAME
//! in-browser verified executor (`starbridge_v2::world::World`) the native cockpit
//! drives. ALONGSIDE the cockpit, two real working panes are mounted in a right
//! dock column:
//!
//!   * [`WebEditorPane`] — a firmament-backed editor over deos-zed's gpui-free
//!     [`FirmamentFs`](deos_zed::fs::FirmamentFs) (an [`OwnedSpine`](deos_zed::fs::OwnedSpine):
//!     a fresh in-tab `Ledger` + `TurnExecutor`). A SAVE is a real cap-gated
//!     `SetField` turn leaving a verifiable `TurnReceipt`; the status line reads
//!     the GENUINE on-ledger receipt count. The gpui editor view is rendered HERE
//!     (deos-zed's own `editor.rs` is `gui`-gated = native-only); the wasm-safe
//!     part we reuse is the executor-backed `Fs`.
//!
//!   * [`WebChatPane`] — a chat view over deos-matrix's gpui-free
//!     [`MockSource`](deos_matrix::source::MockSource) `ChatSource` (a recorded
//!     sync — rooms, timelines, a composer that appends locally). The gpui
//!     `ChatView` is `gui`-gated = native-only; the wasm-safe part we reuse is the
//!     `ChatSource` data seam (the live `MatrixHandle` drops in behind it
//!     unchanged). The chat element tree is rendered HERE.
//!
//! Both pane element trees render on the HOST's `gpui_web` — we do NOT pull
//! deos-zed/deos-matrix's own `gui`/`cockpit-surface` (those link gpui's native
//! windowing, which cannot reach wasm32). One gpui_web canvas paints the cockpit +
//! both panes together.
//!
//! See docs/deos/WEB-DEOS.md.

#![cfg(all(target_arch = "wasm32", feature = "gpui-web"))]

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use gpui::prelude::FluentBuilder as _;
use gpui::{
    div, px, rgb, App, AppContext, Bounds, Context, Entity, FocusHandle, InteractiveElement as _,
    IntoElement, ParentElement as _, Render, SharedString, StatefulInteractiveElement as _,
    Styled as _, Window, WindowBounds, WindowOptions,
};
use gpui_component::input::{Input, InputState};
use wasm_bindgen::prelude::*;

use starbridge_v2::cockpit::Cockpit;
use starbridge_v2::world;

use deos_matrix::client::TimelineMessage;
use deos_matrix::source::{ChatSource, MockSource};
use deos_zed::fs::{Fs, OwnedSpine};

/// THE WASM ENTRYPOINT — boot the FULL gpui cockpit (with the editor + chat panes)
/// in the browser.
///
/// Seeds a fresh sovereign genesis image, boots a single-threaded web gpui
/// application, registers the cockpit fonts + the gpui-component widget globals,
/// opens a window (which creates the WebGPU canvas + appends it to the document
/// body), and mounts the [`WebCockpitRoot`] — the cockpit beside the live editor +
/// chat panes. The gpui run-loop drives paints/events thereafter — every affordance
/// click is a real cap-gated turn through the verified executor in-tab; every
/// editor save is a receipted `SetField` turn on the in-tab `FirmamentFs`.
#[wasm_bindgen]
pub fn boot_cockpit() {
    gpui_platform::web_init();

    // The genesis (at-rest) image + the deferred demo seed — exactly the native
    // `run_window` shape. `with_node` takes the seed so the cockpit seeds it in
    // LIVE (cells appear as each turn commits) off the first-paint path.
    let (world, anchors, seed) = world::demo_genesis();
    let shared = Rc::new(RefCell::new(world));

    gpui_platform::single_threaded_web().run(move |cx: &mut App| {
        // Register the cockpit's fonts. The web platform text system does not carry
        // "Lilex" (the cockpit's default) or "IBM Plex" — without them the styled
        // panels render with blank text (chrome lays out, no glyphs). Same fonts
        // the native boot + the headless bake register.
        static LILEX: &[u8] = include_bytes!("../../assets/fonts/Lilex-Regular.ttf");
        static IBM_PLEX: &[u8] = include_bytes!("../../assets/fonts/IBMPlexSans-Regular.ttf");
        if let Err(e) = cx.text_system().add_fonts(vec![
            std::borrow::Cow::Borrowed(LILEX),
            std::borrow::Cow::Borrowed(IBM_PLEX),
        ]) {
            web_sys_warn(&format!("failed to register embedded UI fonts: {e}"));
        }

        // Initialize gpui-component — the real widget library (text `Input`,
        // `Button`, the shadcn-style set). This installs the theme + the global
        // state every widget reads; without it any gpui-component widget the
        // cockpit (or our panes) constructs panics on a missing global. One call at
        // boot, exactly as native `run_window` does.
        gpui_component::init(cx);

        let bounds = Bounds {
            origin: gpui::point(px(0.), px(0.)),
            size: gpui::size(px(1280.), px(820.)),
        };
        let mut seed = Some(seed);
        cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                ..Default::default()
            },
            move |window, cx| {
                let pending_seed = seed.take();
                let cockpit = cx.new(|cx| {
                    let focus = cx.focus_handle();
                    // The REAL cockpit over the in-browser `World`. `node_url = None`
                    // (no remote-federation panel on the web boot — the data plane is
                    // the in-tab executor); `pending_seed` lets it seed in live.
                    Cockpit::with_node(shared.clone(), anchors, focus, None, pending_seed)
                });
                cockpit.update(cx, |c, cx| c.focus_on_open(window, cx));

                // THE TWO MOUNTED PANES — built on the same window/cx so they paint
                // into the same gpui_web canvas as the cockpit.
                let editor = cx.new(|cx| WebEditorPane::new(window, cx));
                let chat = cx.new(|cx| WebChatPane::new(window, cx));

                cx.new(|cx| WebCockpitRoot::new(cockpit, editor, chat, cx))
            },
        )
        .expect("failed to open web window");
    });
}

/// THE ROOT VIEW — lays out the cockpit beside the editor + chat dock column.
///
/// The cockpit fills the main area; a fixed-width right column stacks the editor
/// pane (top) over the chat pane (bottom). All three are real `gpui` entities
/// rendered into the one `gpui_web` canvas — the panes are not a separate window,
/// they are part of the painted cockpit (so the headless paint-check sees them).
pub struct WebCockpitRoot {
    cockpit: Entity<Cockpit>,
    editor: Entity<WebEditorPane>,
    chat: Entity<WebChatPane>,
}

impl WebCockpitRoot {
    fn new(
        cockpit: Entity<Cockpit>,
        editor: Entity<WebEditorPane>,
        chat: Entity<WebChatPane>,
        _cx: &mut Context<Self>,
    ) -> Self {
        WebCockpitRoot {
            cockpit,
            editor,
            chat,
        }
    }
}

impl Render for WebCockpitRoot {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
        div()
            .flex()
            .flex_row()
            .size_full()
            .bg(rgb(0x0b0d12))
            // The cockpit fills the remaining space.
            .child(div().flex_1().h_full().min_w(px(0.)).child(self.cockpit.clone()))
            // The right dock column: editor over chat.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .w(px(420.))
                    .h_full()
                    .border_l_1()
                    .border_color(rgb(0x222838))
                    .child(div().flex_1().min_h(px(0.)).child(self.editor.clone()))
                    .child(
                        div()
                            .flex_1()
                            .min_h(px(0.))
                            .border_t_1()
                            .border_color(rgb(0x222838))
                            .child(self.chat.clone()),
                    ),
            )
    }
}

// ============================================================================
// THE EDITOR PANE — over deos-zed's gpui-free FirmamentFs (OwnedSpine).
// ============================================================================

/// The seed file the editor opens onto (a single on-ledger file-cell). Saving it
/// fires a real cap-gated `SetField` turn through the in-tab `TurnExecutor`.
const EDITOR_SEED_PATH: &str = "/deos/main.rs";
const EDITOR_SEED_CONTENT: &str = "// edit me — every save here is a RECEIPTED dregg turn on the in-tab ledger.\n\
fn main() {\n    println!(\"hello from a sovereign cell\");\n}\n";

/// A firmament-backed editor pane: the buffer edits a sovereign cell on a fresh
/// in-tab [`OwnedSpine`] (`Ledger` + `TurnExecutor`); a SAVE is a real `SetField`
/// turn leaving a verifiable [`TurnReceipt`](dregg_turn::TurnReceipt). The gpui
/// editor view is rendered here (deos-zed's own gpui `Editor` is native-only); the
/// wasm-safe reuse is the executor-backed [`Fs`].
pub struct WebEditorPane {
    /// The in-tab firmament fs — its `save` is the receipt-producing turn.
    fs: deos_zed::fs::FirmamentFs,
    /// The path of the open file-cell on the spine.
    path: std::path::PathBuf,
    /// The editable buffer (a real `gpui-component` rope-backed `Input`).
    buffer: Entity<InputState>,
    /// The status line: the GENUINE on-ledger receipt count + the last receipt's
    /// post-state digest after a save.
    status: SharedString,
    focus: FocusHandle,
}

impl WebEditorPane {
    fn new(window: &mut Window, cx: &mut Context<Self>) -> Self {
        // A fresh in-tab firmament fs over its OWN spine (ledger + executor). On
        // wasm32 deos-zed resolves the no-Lean-link executor — the SAME in-browser
        // executor starbridge-web drives. `FirmamentFs::new()` builds over an
        // `OwnedSpine`.
        let _ = OwnedSpine::new; // documents the backing spine type.
        let fs = deos_zed::fs::FirmamentFs::new();
        let path = std::path::PathBuf::from(EDITOR_SEED_PATH);
        // Seed the file-cell so there is something editable + a real cell to save
        // against (the first save is then a SetField on an existing cell).
        let seed_status = match fs.seed_file(&path, EDITOR_SEED_CONTENT) {
            Ok(_cell) => SharedString::from(format!(
                "{} · {} saves · on-ledger",
                fs.backend_label(),
                fs.save_count().unwrap_or(0)
            )),
            Err(e) => SharedString::from(format!("seed failed: {e}")),
        };

        let initial = fs.load(&path).unwrap_or_else(|_| EDITOR_SEED_CONTENT.to_string());
        let buffer = cx.new(|cx| {
            let mut st = InputState::new(window, cx).multi_line(true);
            st.set_value(&initial, window, cx);
            st
        });

        WebEditorPane {
            fs,
            path,
            buffer,
            status: seed_status,
            focus: cx.focus_handle(),
        }
    }

    /// SAVE — write the buffer to the file-cell. With `FirmamentFs` this is a real
    /// cap-gated `SetField` turn through the in-tab `TurnExecutor`, leaving a
    /// verifiable `TurnReceipt`. Updates the status line with the genuine receipt
    /// count + the last post-state digest.
    fn save(&mut self, _window: &mut Window, cx: &mut Context<Self>) {
        let content = self.buffer.read(cx).value().to_string();
        match self.fs.save(&self.path, &content) {
            Ok(()) => {
                let n = self.fs.save_count().unwrap_or(0);
                let digest = self
                    .fs
                    .last_receipt()
                    .map(|r| {
                        let h = hex::encode(r.post_state_hash);
                        format!("{}…{}", &h[..6], &h[h.len() - 4..])
                    })
                    .unwrap_or_else(|| "—".into());
                self.status = SharedString::from(format!(
                    "{} · {n} saves · on-ledger · post {digest}",
                    self.fs.backend_label()
                ));
            }
            Err(e) => {
                self.status = SharedString::from(format!("save refused: {e}"));
            }
        }
        cx.notify();
    }
}

impl Render for WebEditorPane {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        div()
            .id("web-editor-pane")
            .track_focus(&self.focus)
            .flex()
            .flex_col()
            .size_full()
            .bg(rgb(0x0e1117))
            .text_color(rgb(0xc8d0e0))
            // Title bar.
            .child(
                div()
                    .flex()
                    .flex_row()
                    .items_center()
                    .justify_between()
                    .px_3()
                    .py_2()
                    .bg(rgb(0x151a23))
                    .border_b_1()
                    .border_color(rgb(0x222838))
                    .child(
                        div()
                            .text_sm()
                            .text_color(rgb(0xe6ebf5))
                            .child(SharedString::from(format!("editor · {}", EDITOR_SEED_PATH))),
                    )
                    .child(
                        div()
                            .id("web-editor-save")
                            .px_2()
                            .py_1()
                            .bg(rgb(0x2b6cb0))
                            .text_color(rgb(0xffffff))
                            .text_xs()
                            .cursor_pointer()
                            .child("save (turn)")
                            .on_click(cx.listener(|this, _ev, window, cx| this.save(window, cx))),
                    ),
            )
            // The editable buffer.
            .child(
                div()
                    .flex_1()
                    .min_h(px(0.))
                    .p_2()
                    .child(Input::new(&self.buffer).h_full()),
            )
            // Status line: the genuine on-ledger receipt truth.
            .child(
                div()
                    .px_3()
                    .py_1()
                    .bg(rgb(0x151a23))
                    .border_t_1()
                    .border_color(rgb(0x222838))
                    .text_xs()
                    .text_color(rgb(0x8aa0c0))
                    .child(self.status.clone()),
            )
    }
}

// ============================================================================
// THE CHAT PANE — over deos-matrix's gpui-free MockSource ChatSource.
// ============================================================================

/// How many recent messages to pull per room (mirrors the native ChatView limit).
const TIMELINE_LIMIT: u16 = 80;

/// A chat pane over the gpui-free [`ChatSource`] seam ([`MockSource`] here — a
/// recorded sync). Renders a room sidebar + the selected room's timeline + a
/// composer. The live `MatrixHandle` (matrix-sdk's wasm IndexedDB/spawn_local
/// client) drops in behind the SAME trait unchanged.
pub struct WebChatPane {
    source: Arc<dyn ChatSource>,
    me: Option<String>,
    rooms: Vec<deos_matrix::client::RoomSummary>,
    selected: Option<usize>,
    timeline: Vec<TimelineMessage>,
    composer: Entity<InputState>,
    status: SharedString,
    focus: FocusHandle,
}

impl WebChatPane {
    fn new(window: &mut Window, cx: &mut Context<Self>) -> Self {
        let source: Arc<dyn ChatSource> = Arc::new(MockSource::seeded());
        let me = source.whoami();
        let rooms = source.rooms().unwrap_or_default();
        let selected = if rooms.is_empty() { None } else { Some(0) };
        let timeline = selected
            .and_then(|i| rooms.get(i))
            .map(|r| {
                source
                    .timeline(&r.room_id.to_string(), TIMELINE_LIMIT)
                    .unwrap_or_default()
            })
            .unwrap_or_default();
        let composer = cx.new(|cx| InputState::new(window, cx));
        let status = SharedString::from(format!(
            "{} · {} rooms",
            source.backend_label(),
            rooms.len()
        ));
        WebChatPane {
            source,
            me,
            rooms,
            selected,
            timeline,
            composer,
            status,
            focus: cx.focus_handle(),
        }
    }

    fn select_room(&mut self, idx: usize, _window: &mut Window, cx: &mut Context<Self>) {
        if idx >= self.rooms.len() {
            return;
        }
        self.selected = Some(idx);
        let rid = self.rooms[idx].room_id.to_string();
        self.timeline = self
            .source
            .timeline(&rid, TIMELINE_LIMIT)
            .unwrap_or_default();
        cx.notify();
    }

    /// SEND — append the composer's contents to the selected room (the mock echoes
    /// a local event id; the live backend POSTs + the next sync folds the echo in),
    /// then refresh the timeline + clear the composer.
    fn send(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        let Some(idx) = self.selected else { return };
        let body = self.composer.read(cx).value().to_string();
        if body.trim().is_empty() {
            return;
        }
        let rid = self.rooms[idx].room_id.to_string();
        match self.source.send_turn(&rid, &body) {
            Ok(receipt) => {
                self.status = SharedString::from(format!(
                    "{} · turn {} · event {}",
                    self.source.backend_label(),
                    receipt.turn_index,
                    receipt.event_id
                ));
            }
            Err(e) => {
                self.status = SharedString::from(format!("send failed: {e}"));
            }
        }
        self.composer
            .update(cx, |st, cx| st.set_value("", window, cx));
        self.timeline = self
            .source
            .timeline(&rid, TIMELINE_LIMIT)
            .unwrap_or_default();
        cx.notify();
    }
}

impl Render for WebChatPane {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let me = self.me.clone().unwrap_or_default();

        // Room sidebar.
        let mut rooms_col = div().flex().flex_col().w(px(120.)).h_full().bg(rgb(0x0e1117));
        for (i, r) in self.rooms.iter().enumerate() {
            let selected = self.selected == Some(i);
            rooms_col = rooms_col.child(
                div()
                    .id(("web-chat-room", i))
                    .px_2()
                    .py_1()
                    .text_xs()
                    .when(selected, |d| d.bg(rgb(0x223052)))
                    .text_color(if selected { rgb(0xe6ebf5) } else { rgb(0x9aa8c0) })
                    .cursor_pointer()
                    .child(SharedString::from(r.display_name.clone()))
                    .on_click(cx.listener(move |this, _ev, window, cx| {
                        this.select_room(i, window, cx)
                    })),
            );
        }

        // Timeline.
        let mut tl_col = div().flex().flex_col().flex_1().min_w(px(0.)).p_2().gap_1();
        for m in &self.timeline {
            let mine = m.sender == me;
            tl_col = tl_col.child(
                div()
                    .flex()
                    .flex_col()
                    .child(
                        div()
                            .text_xs()
                            .text_color(if mine { rgb(0x6cb0ff) } else { rgb(0x88c08a) })
                            .child(SharedString::from(m.sender.clone())),
                    )
                    .child(
                        div()
                            .text_sm()
                            .text_color(rgb(0xc8d0e0))
                            .child(SharedString::from(m.body.clone())),
                    ),
            );
        }

        div()
            .id("web-chat-pane")
            .track_focus(&self.focus)
            .flex()
            .flex_col()
            .size_full()
            .bg(rgb(0x0b0d12))
            // Title.
            .child(
                div()
                    .px_3()
                    .py_2()
                    .bg(rgb(0x151a23))
                    .border_b_1()
                    .border_color(rgb(0x222838))
                    .text_sm()
                    .text_color(rgb(0xe6ebf5))
                    .child("chat · membrane-bearing"),
            )
            // Sidebar + timeline.
            .child(
                div()
                    .flex()
                    .flex_row()
                    .flex_1()
                    .min_h(px(0.))
                    .child(rooms_col)
                    .child(tl_col),
            )
            // Composer.
            .child(
                div()
                    .flex()
                    .flex_row()
                    .items_center()
                    .gap_2()
                    .px_2()
                    .py_2()
                    .border_t_1()
                    .border_color(rgb(0x222838))
                    .child(div().flex_1().min_w(px(0.)).child(Input::new(&self.composer)))
                    .child(
                        div()
                            .id("web-chat-send")
                            .px_2()
                            .py_1()
                            .bg(rgb(0x2b6cb0))
                            .text_color(rgb(0xffffff))
                            .text_xs()
                            .cursor_pointer()
                            .child("send")
                            .on_click(cx.listener(|this, _ev, window, cx| this.send(window, cx))),
                    ),
            )
            // Status line.
            .child(
                div()
                    .px_3()
                    .py_1()
                    .bg(rgb(0x151a23))
                    .border_t_1()
                    .border_color(rgb(0x222838))
                    .text_xs()
                    .text_color(rgb(0x8aa0c0))
                    .child(self.status.clone()),
            )
    }
}

/// Surface a warning to the browser console (the web platform has no stderr).
fn web_sys_warn(msg: &str) {
    web_sys::console::warn_1(&JsValue::from_str(msg));
}
