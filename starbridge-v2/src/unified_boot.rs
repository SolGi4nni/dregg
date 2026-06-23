//! THE ONE UNIFIED BOOT — node + cockpit-panes in a SINGLE window/frame.
//!
//! [`crate::self_hosting`] proves the editor↔terminal self-hosting loop over an
//! EMBEDDED `World`. This view proves the OTHER unification: the same cockpit
//! panes (FirmamentFs editor + live PTY terminal) standing ALONGSIDE a LIVE
//! `--node`-attached pane whose cells/receipts/status come from a real running
//! `dregg-node` over the wire (`/status` + `/api/cells` + `/api/receipts`),
//! reflected through the SAME [`crate::live_node::LiveReflection`] the cockpit's
//! own live-node strip uses — not a mock.
//!
//! Three panes, one frame:
//!
//!   * **LIVE NODE** — a real [`crate::client::LiveNode::sync`] snapshot of the
//!     attached node: its `/status` (lean producer, height, dag) + every live
//!     cell + the latest receipt, each projected into the uniform reflective
//!     model. This is what proves the attach is LIVE, not embedded: the cells and
//!     the receipt shown are the node's, pulled over HTTP at build time.
//!
//!   * **EDITOR** — a [`crate::dock::editor_surface::EditorPane::firmament_over`]
//!     the cockpit's LOCAL `World`. A save is a cap-gated `SetField` turn on that
//!     LOCAL ledger. (The write-back seam — whether that turn reaches the NODE's
//!     ledger — is exercised + reported by the headless bake, not papered over:
//!     today the save lands on the cockpit World, the node is read-only-synced.)
//!
//!   * **TERMINAL** — a live alacritty PTY running a real command INSIDE deos.
//!
//! The headless bake (`--render-unified-boot` in `main.rs`) wires all three over a
//! running node, drives a real editor save, re-reads the node's receipt count to
//! settle the write-back question empirically, and captures the PNG.

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, px, App, AppContext, Context, Entity, FocusHandle, Focusable, InteractiveElement,
    IntoElement, ParentElement, Render, Styled, Window,
};

use crate::client::{LiveNode, LiveSnapshot};
use crate::dock::editor_surface::EditorPane;
use crate::dock::surface::CockpitSurface;
use crate::dock::terminal_surface::TerminalPane;
use crate::reflect::{Field, FieldValue, Inspectable, ObjectKind};
use crate::world::World;

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
    pub fn good() -> Hsla {
        rgb(0x5bd18b).into()
    }
    pub fn warn() -> Hsla {
        rgb(0xe3b341).into()
    }
}

/// The seed project the firmament editor opens onto, installed on the LOCAL
/// cockpit `World`. A save here is a receipted turn on THAT ledger.
const UNIFIED_SEED: &[(&str, &str)] = &[(
    "/main.rs",
    "// edit me — a save is a cap-gated SetField turn (a real TurnReceipt) on the\n\
     // cockpit's LOCAL World ledger. The live-node pane to the left reflects a\n\
     // SEPARATE, real running dregg-node over the wire.\n\
     fn main() {\n    println!(\"v1\");\n}\n",
)];

/// The root view mounting all three unified-boot panes.
pub struct UnifiedBootView {
    /// A wrapped client to the attached node, so the bake can RE-READ the node's
    /// live receipt/cell count after an editor save (the write-back probe).
    live_node: Option<LiveNode>,
    /// The last fetched live snapshot of the attached node (status + cells).
    snapshot: Option<LiveSnapshot>,
    /// The latest receipt reflected from the node (the live provenance head).
    receipt_view: Option<Inspectable>,
    editor: EditorPane,
    terminal: TerminalPane,
    /// The local cockpit `World` the editor saves into.
    world: Rc<RefCell<World>>,
    focus: FocusHandle,
}

impl UnifiedBootView {
    /// Build the unified-boot view: the live-node pane (a real snapshot of the
    /// node at `node_url`, if reachable) + a firmament editor over `world` + a
    /// live-PTY terminal. An unreachable / absent node leaves the pane showing
    /// "(no node attached)" and the editor+terminal fully live — honest.
    pub fn build(
        world: Rc<RefCell<World>>,
        node_url: Option<String>,
        terminal_cmd: Option<(String, Vec<String>)>,
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        let root = std::env::current_dir().unwrap_or_else(|_| std::path::PathBuf::from("."));

        // LIVE NODE — wrap a real HTTP client and take ONE blocking snapshot. This
        // is the SAME `LiveNode::sync` the cockpit's `--node` attach uses; the
        // cells/receipts shown are the node's, pulled over the wire right now.
        let (live_node, snapshot, receipt_view) = match node_url {
            Some(url) => {
                let ln = LiveNode::new(crate::client::NodeClient::http(url));
                let snap = ln.sync().ok();
                // The latest committed receipt. `/api/receipts` returns the FULL
                // receipt shape (a superset of the SSE-summary `ReceiptEvent`), so
                // the typed `receipts()` parse rejects it; reflect the raw JSON of
                // the chain head directly — the genuine on-node provenance node.
                let receipt = ln
                    .client()
                    .receipts_raw()
                    .ok()
                    .and_then(|rs| rs.into_iter().next())
                    .map(|raw| raw_receipt_inspectable(&raw));
                (Some(ln), snap, receipt)
            }
            None => (None, None, None),
        };

        // EDITOR — firmament over the LOCAL cockpit World (a save = a real turn on
        // THAT ledger). This is the write-back seam under test.
        let editor =
            EditorPane::firmament_over(1, world.clone(), root.clone(), UNIFIED_SEED, window, cx)?;

        // TERMINAL — a live PTY running a real command.
        let terminal = TerminalPane::spawn(2, terminal_cmd, cx)?;

        Ok(Self {
            live_node,
            snapshot,
            receipt_view,
            editor,
            terminal,
            world,
            focus: cx.focus_handle(),
        })
    }

    /// Fire a REAL editor save (set buffer + the editor's genuine `save`, a
    /// cap-gated `SetField` turn through the verified executor on the LOCAL
    /// World). Returns the LOCAL on-ledger receipt count after the save.
    pub fn fire_save(
        &self,
        content: &str,
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<usize> {
        let editor = self.editor.editor().clone();
        editor.update(cx, |ed, cx| {
            ed.set_text(content, window, cx);
            ed.save(cx)
        })?;
        Ok(self.editor.receipt_count().unwrap_or(0))
    }

    /// The local cockpit World's receipt count (the editor-save ledger).
    pub fn world_receipt_count(&self) -> usize {
        self.world.borrow().receipts().len()
    }

    /// RE-READ the ATTACHED NODE's live receipt count over the wire — the
    /// write-back probe. If an editor save reaches the node's ledger, this grows;
    /// if the save is local-only (today's reality), it does not. `None` if no node.
    pub fn node_receipt_count(&self) -> Option<usize> {
        let ln = self.live_node.as_ref()?;
        ln.client().receipts_count().ok()
    }

    /// RE-READ the attached node's live cell count over the wire.
    pub fn node_cell_count(&self) -> Option<usize> {
        let ln = self.live_node.as_ref()?;
        ln.client().cells().ok().map(|cs| cs.len())
    }

    /// Whether a node is attached AND its last snapshot reported the lean producer.
    pub fn node_lean_producer(&self) -> Option<bool> {
        self.snapshot.as_ref().map(|s| s.status.lean_producer)
    }

    /// Write a line to the live PTY (e.g. a command + `\n`).
    pub fn terminal_input(&self, s: &str, cx: &App) {
        self.terminal.view().read(cx).terminal.write_str(s);
    }

    /// Scrape the terminal grid into a newline-joined string (the live child's
    /// genuine on-grid output, for the host to assert against).
    pub fn terminal_text(&self, cx: &App) -> String {
        let content = self.terminal.view().read(cx).terminal.content();
        let cols = content.columns.max(1);
        let rows = content.screen_lines.max(1);
        let mut grid = vec![vec![' '; cols]; rows];
        for cell in &content.cells {
            let line = cell.line;
            if line < 0 {
                continue;
            }
            let (r, c) = (line as usize, cell.column);
            if r < rows && c < cols {
                grid[r][c] = cell.c;
            }
        }
        grid.into_iter()
            .map(|row| row.into_iter().collect::<String>().trim_end().to_string())
            .collect::<Vec<_>>()
            .join("\n")
    }
}

impl Focusable for UnifiedBootView {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for UnifiedBootView {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let editor_body = self.editor.render_body(window, cx);
        let terminal_body = self.terminal.render_body(window, cx);

        let local_receipts = self.world_receipt_count();
        let local_height = self.world.borrow().height();
        let local_cells = self.world.borrow().cell_count();

        let header = div()
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
                    .child("deos · UNIFIED BOOT — live node + editor + terminal, one window"),
            )
            .child(badge(&format!("local h{local_height}"), theme::accent()))
            .child(badge(&format!("{local_cells} local cells"), theme::accent()))
            .child(badge(
                &format!("{local_receipts} local receipts"),
                theme::accent(),
            ));

        let node_pane = framed(
            "live node · --node (a real running dregg-node, over the wire)",
            "its /status + cells + latest receipt, reflected live",
            self.render_node_pane(),
        );
        let editor_pane = framed(
            "editor · deos-zed (firmament over the cockpit's LOCAL World)",
            "a save = a cap-gated SetField turn → a real TurnReceipt (local ledger)",
            editor_body,
        );
        let terminal_pane = framed(
            "terminal · deos-terminal (live alacritty PTY)",
            "real cargo/git running INSIDE deos",
            terminal_body,
        );

        div()
            .key_context("UnifiedBoot")
            .track_focus(&self.focus)
            .flex()
            .flex_col()
            .size_full()
            .bg(theme::bg())
            .text_color(theme::text())
            .font_family("Menlo")
            .child(header)
            .child(
                div()
                    .flex()
                    .gap_3()
                    .flex_1()
                    .min_h(px(0.))
                    .w_full()
                    .p_3()
                    .child(node_pane)
                    .child(editor_pane)
                    .child(terminal_pane),
            )
    }
}

impl UnifiedBootView {
    /// Render the live-node pane body from the fetched snapshot + receipt.
    fn render_node_pane(&self) -> gpui::AnyElement {
        let mut col = div().flex().flex_col().gap_2().p_2().size_full();

        match &self.snapshot {
            Some(s) => {
                let st = &s.status;
                col = col.child(
                    div()
                        .flex()
                        .flex_wrap()
                        .gap_1()
                        .items_center()
                        .child(pill(
                            if st.healthy { "healthy" } else { "DOWN" },
                            if st.healthy { theme::good() } else { theme::warn() },
                        ))
                        .child(pill(
                            &format!("producer {}", st.state_producer),
                            if st.lean_producer { theme::good() } else { theme::warn() },
                        ))
                        .child(pill(&format!("h{}", st.latest_height), theme::accent()))
                        .child(pill(&format!("dag {}", st.dag_height), theme::muted()))
                        .child(pill(
                            &format!("{} effects", st.producer_covered_effects),
                            theme::muted(),
                        )),
                );
                col = col.child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(format!("{} live cells · synced over /api/cells", s.cell_views.len())),
                );
                for cv in s.cell_views.iter().take(4) {
                    col = col.child(inspectable_card(cv));
                }
            }
            None => {
                col = col.child(
                    div()
                        .text_color(theme::warn())
                        .child("(no node attached / unreachable)"),
                );
            }
        }

        if let Some(rv) = &self.receipt_view {
            col = col.child(
                div()
                    .mt_1()
                    .text_xs()
                    .text_color(theme::accent())
                    .child("LATEST NODE RECEIPT · /api/receipts"),
            );
            col = col.child(inspectable_card(rv));
        }

        col.into_any_element()
    }
}

/// Reflect a raw `/api/receipts` JSON node (the FULL receipt shape) into the
/// uniform [`Inspectable`] the live-node pane renders — the genuine on-node
/// provenance head, drawn straight from the node's own receipt record.
fn raw_receipt_inspectable(raw: &serde_json::Value) -> Inspectable {
    let s = |k: &str| raw.get(k).and_then(|v| v.as_str()).unwrap_or("").to_string();
    let n = |k: &str| raw.get(k).and_then(|v| v.as_u64()).unwrap_or(0);
    let b = |k: &str| raw.get(k).and_then(|v| v.as_bool()).unwrap_or(false);
    let receipt_hash = s("receipt_hash");
    let fields = vec![
        Field::text("receipt_hash", short(&receipt_hash)),
        Field::text("turn_hash", short(&s("turn_hash"))),
        Field::count("chain_index", n("chain_index")),
        Field::text("pre_state", short(&s("pre_state"))),
        Field::text("post_state", short(&s("post_state"))),
        Field::count("action_count", n("action_count")),
        Field::count("computrons_used", n("computrons_used")),
        Field::boolean("has_proof", b("has_proof")),
        Field::boolean("executor_signed", b("executor_signed")),
        Field::boolean("has_witness", b("has_witness")),
        Field::text("finality", s("finality")),
    ];
    Inspectable {
        kind: ObjectKind::Receipt,
        title: format!("Receipt {}", short(&receipt_hash)),
        subtitle: format!(
            "node · #{} · {} actions · {} computrons",
            n("chain_index"),
            n("action_count"),
            n("computrons_used")
        ),
        fields,
    }
}

/// First 8 + last 4 hex chars of a long id, for compact display.
fn short(hex: &str) -> String {
    if hex.len() <= 16 {
        hex.to_string()
    } else {
        format!("{}…{}", &hex[..8], &hex[hex.len() - 4..])
    }
}

/// A self-contained card for a reflected node object (status/cell/receipt) — the
/// uniform [`Inspectable`] shape, rendered without reaching into the cockpit's
/// `pub(crate)` helpers.
fn inspectable_card(ins: &Inspectable) -> impl IntoElement {
    let mut card = div()
        .flex()
        .flex_col()
        .gap_0p5()
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .child(div().text_xs().text_color(theme::text()).child(ins.title.clone()))
        .child(div().text_xs().text_color(theme::muted()).child(ins.subtitle.clone()));
    for f in ins.fields.iter().take(6) {
        let (val, color) = field_display(&f.value);
        card = card.child(
            div()
                .flex()
                .justify_between()
                .child(div().text_xs().text_color(theme::muted()).child(f.key.clone()))
                .child(div().text_xs().text_color(color).child(val)),
        );
    }
    card
}

fn field_display(v: &FieldValue) -> (String, gpui::Hsla) {
    match v {
        FieldValue::Text(s) => (s.clone(), theme::text()),
        FieldValue::Balance(b) => (
            b.to_string(),
            if *b < 0 { theme::warn() } else { theme::text() },
        ),
        FieldValue::Count(c) => (c.to_string(), theme::text()),
        FieldValue::Bool(b) => (b.to_string(), if *b { theme::good() } else { theme::muted() }),
        FieldValue::Id(id) => (crate::reflect::short_hex(id), theme::accent()),
        FieldValue::Hash(h) => (crate::reflect::short_hex(h), theme::good()),
        FieldValue::CapEdge { target, slot } => (
            format!("→ {} (slot {slot})", crate::reflect::short_hex(target)),
            theme::accent(),
        ),
        FieldValue::FieldSlot { hex, .. } => {
            (crate::reflect::short_hex_hexstr(hex), theme::muted())
        }
    }
}

/// Mount the unified-boot view as a root view for the headless capture.
pub fn build_root(
    world: Rc<RefCell<World>>,
    node_url: Option<String>,
    terminal_cmd: Option<(String, Vec<String>)>,
    window: &mut Window,
    cx: &mut App,
) -> anyhow::Result<Entity<UnifiedBootView>> {
    let view = cx.new(|cx| {
        UnifiedBootView::build(world, node_url, terminal_cmd, window, cx)
            .expect("unified-boot view mount")
    });
    view.update(cx, |v, cx| {
        let focus = v.focus.clone();
        focus.focus(window, cx);
    });
    Ok(view)
}

fn badge(text: &str, color: gpui::Hsla) -> impl IntoElement {
    div()
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_color(color)
        .text_xs()
        .child(text.to_string())
}

fn pill(text: &str, color: gpui::Hsla) -> impl IntoElement {
    div()
        .px_1p5()
        .py_0p5()
        .rounded_md()
        .bg(theme::panel())
        .border_1()
        .border_color(theme::border())
        .text_color(color)
        .text_xs()
        .child(text.to_string())
}

fn framed(title: &str, subtitle: &str, body: gpui::AnyElement) -> impl IntoElement {
    div()
        .flex()
        .flex_col()
        .flex_1()
        .min_w(px(0.))
        .h_full()
        .rounded_md()
        .border_1()
        .border_color(theme::border())
        .bg(theme::panel())
        .child(
            div()
                .flex()
                .flex_col()
                .gap_0p5()
                .px_3()
                .py_2()
                .border_b_1()
                .border_color(theme::border())
                .child(div().text_color(theme::text()).child(title.to_string()))
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(subtitle.to_string()),
                ),
        )
        .child(div().flex_1().min_h(px(0.)).overflow_hidden().child(body))
}
