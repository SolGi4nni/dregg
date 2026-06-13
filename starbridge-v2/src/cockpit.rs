//! The gpui cockpit — the comprehensive visual master interface.
//!
//! This is the visual layer (gpui-gated, `native-full` only). It renders the
//! embedded [`World`](crate::world::World) — the live local dregg image — across
//! the four dregg-surpasses-Smalltalk axes, each a panel:
//!
//!   * CELL WORLD (left rail) — every cell as a live object; click to inspect.
//!     The ocap axis: the cap count + the graph edges are first-class.
//!   * INSPECTOR (center) — the selected object reflected through the uniform
//!     [`reflect`](crate::reflect) model: cell ⟷ receipt ⟷ image, navigable.
//!   * BLOCKLACE (center-low) — the provenance axis: the receipt chain as a
//!     navigable causal history (time-travel).
//!   * COMPOSER (right) — direct-manipulation turn composition: pick a verb,
//!     watch the EMBEDDED EXECUTOR run it and the image + receipts update live.
//!   * DYNAMICS (right-low) — the live activity feed off the dynamics stream.
//!   * IMAGE/FEDERATION (rail header) — the distribution axis: this image's
//!     state-root commitment, presented as one sovereign image among a
//!     federation.
//!
//! gpui is single-threaded; the `World` is shared as `Rc<RefCell<World>>`. Every
//! verb button mutates it through `World::commit_turn` (the REAL executor) and
//! the views re-render from the post-state on the next frame.

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, prelude::*, px, Context, Hsla, IntoElement, MouseButton, ParentElement, Render,
    SharedString, Styled, Window,
};

use dregg_cell::CellId;

use crate::views::{pill, section_title, theme};
use starbridge_v2::dynamics;
use starbridge_v2::reflect::{self, Field, FieldValue, Inspectable, ObjectKind};
use starbridge_v2::world::{self, CommitOutcome, World};

/// Which object the inspector is focused on.
#[derive(Clone)]
pub enum Selection {
    Cell(CellId),
    Receipt(usize),
    Image,
}

/// The whole cockpit — owns the shared world + the current selection + a
/// dynamics cursor for the activity feed.
pub struct Cockpit {
    world: Rc<RefCell<World>>,
    /// Stable, sorted list of cell ids (so the rail order is deterministic and
    /// selection survives across commits).
    cells: Vec<CellId>,
    selection: Selection,
    /// The last action's outcome banner (committed hash / rejection reason).
    last_outcome: Option<String>,
    /// Three anchor cells for the demo verbs (treasury, service, user).
    anchors: [CellId; 3],
}

impl Cockpit {
    pub fn new(world: Rc<RefCell<World>>, anchors: [CellId; 3]) -> Self {
        let cells = sorted_cells(&world.borrow());
        Self {
            world,
            cells,
            selection: Selection::Image,
            last_outcome: None,
            anchors,
        }
    }

    fn refresh_cells(&mut self) {
        self.cells = sorted_cells(&self.world.borrow());
    }

    // --- the verbs (each runs the REAL embedded executor) -------------------

    fn run_demo_transfer(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(treasury, vec![world::transfer(treasury, user, 1_000)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    fn run_demo_grant(&mut self, cx: &mut Context<Self>) {
        let [_treasury, service, user] = self.anchors;
        // Re-grant the service's user-cap to a fresh slot (legitimate).
        let outcome = {
            let mut w = self.world.borrow_mut();
            let slot = w
                .ledger()
                .get(&service)
                .map(|c| c.capabilities.len() as u32)
                .unwrap_or(0);
            let turn = w.turn(service, vec![world::grant_capability(service, service, user, slot)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    fn run_demo_create(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, _user] = self.anchors;
        let seed = (self.world.borrow().cell_count() as u8).wrapping_add(0x40);
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(treasury, vec![world::create_cell(seed)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    fn run_over_grant(&mut self, cx: &mut Context<Self>) {
        // Demonstrate the ocap guarantee FIRING: an illegitimate grant.
        let [treasury, _service, user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            // treasury holds no cap to user → no-amplification rejects this.
            let turn = w.turn(treasury, vec![world::grant_capability(treasury, treasury, user, 0)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    fn note_outcome(&mut self, outcome: CommitOutcome) {
        self.last_outcome = Some(match outcome {
            CommitOutcome::Committed { receipt, .. } => {
                // Jump the inspector to the new receipt.
                let idx = self.world.borrow().receipts().len().saturating_sub(1);
                self.selection = Selection::Receipt(idx);
                format!("committed · receipt {}", reflect::short_hex(&receipt.receipt_hash()))
            }
            CommitOutcome::Rejected { reason, .. } => format!("REJECTED by executor: {reason}"),
        });
    }

    // --- panels --------------------------------------------------------------

    fn rail_header(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let root = reflect::short_hex(&w.state_root());
        div()
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .border_b_1()
            .border_color(theme::border())
            .child(div().text_lg().text_color(theme::text()).child("Starbridge v2"))
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("the live, verified, ocap image"),
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
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!(
                        "{} cells · {} receipts",
                        w.cell_count(),
                        w.receipts().len()
                    )),
            )
    }

    fn cell_world(&self, cx: &mut Context<Self>) -> impl IntoElement {
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

    fn image_row(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let selected = matches!(self.selection, Selection::Image);
        div()
            .id("image-row")
            .flex()
            .justify_between()
            .px_2()
            .py_1()
            .rounded_md()
            .bg(if selected { theme::panel_hi() } else { theme::panel() })
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

    fn cell_row(&self, id: CellId, cell: &dregg_cell::Cell, cx: &mut Context<Self>) -> impl IntoElement {
        let selected = matches!(self.selection, Selection::Cell(s) if s == id);
        let bal = cell.state.balance();
        let caps = cell.capabilities.len();
        let bal_color = if bal < 0 { theme::warn() } else { theme::text() };
        div()
            .id(SharedString::from(format!("cell-{}", reflect::short_hex(id.as_bytes()))))
            .flex()
            .flex_col()
            .gap_0p5()
            .px_2()
            .py_1()
            .rounded_md()
            .bg(if selected { theme::panel_hi() } else { theme::panel() })
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
                    .child(div().text_color(theme::text()).child(format!("⬡ {}", reflect::short_hex(id.as_bytes()))))
                    .child(div().text_color(bal_color).child(format!("{bal}"))),
            )
            .child(
                div()
                    .flex()
                    .gap_2()
                    .child(div().text_xs().text_color(theme::muted()).child(format!("{caps} caps")))
                    .when(cell.delegate.is_some(), |d| {
                        d.child(div().text_xs().text_color(theme::muted()).child("delegate"))
                    })
                    .when(!matches!(cell.program, dregg_cell::CellProgram::None), |d| {
                        d.child(div().text_xs().text_color(theme::accent()).child("program"))
                    }),
            )
    }

    fn inspector(&self) -> impl IntoElement {
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
                panel = panel.child(
                    div().text_color(theme::text()).child(obj.title.clone()),
                );
                panel = panel.child(
                    div().text_xs().text_color(theme::muted()).mb_2().child(obj.subtitle.clone()),
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

    fn blocklace(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1().p_2();
        col = col.child(section_title("BLOCKLACE · provenance").mb_1());
        if w.receipts().is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child("(no receipts yet — run a verb)"));
        }
        // Most-recent first.
        for (i, r) in w.receipts().iter().enumerate().rev() {
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
                    .bg(if selected { theme::panel_hi() } else { theme::panel() })
                    .cursor_pointer()
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.selection = Selection::Receipt(i);
                            cx.notify();
                        }),
                    )
                    .child(div().text_xs().text_color(theme::accent()).child(format!("●─ {hash}")))
                    .child(div().text_xs().text_color(theme::muted()).child(format!("{} eff", r.action_count))),
            );
        }
        col
    }

    fn composer(&self, cx: &mut Context<Self>) -> impl IntoElement {
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
            .child(verb_button(cx, "transfer 1,000 → user", theme::good(), Cockpit::run_demo_transfer))
            .child(verb_button(cx, "grant capability (service→user)", theme::accent(), Cockpit::run_demo_grant))
            .child(verb_button(cx, "create cell (conserves value)", theme::accent(), Cockpit::run_demo_create))
            .child(verb_button(cx, "⚠ over-grant (watch it REJECT)", theme::warn(), Cockpit::run_over_grant))
            .child(self.outcome_banner())
    }

    fn outcome_banner(&self) -> impl IntoElement {
        let (txt, color) = match &self.last_outcome {
            Some(s) if s.contains("REJECTED") => (s.clone(), theme::bad()),
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

    fn dynamics_feed(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_0p5().p_2();
        col = col.child(section_title("DYNAMICS · live").mb_1());
        let tail = w.dynamics().tail(12);
        if tail.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child("(quiet)"));
        }
        for ev in tail.iter().rev() {
            let is_reject = matches!(ev, dynamics::WorldEvent::TurnRejected { .. });
            col = col.child(
                div()
                    .text_xs()
                    .text_color(if is_reject { theme::bad() } else { theme::muted() })
                    .child(format!("· {}", ev.label())),
            );
        }
        col
    }
}

impl Render for Cockpit {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        div()
            .flex()
            .size_full()
            .bg(theme::bg())
            .text_color(theme::text())
            .font_family("monospace")
            // Left rail: image header + cell world + dynamics feed.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .w(px(320.))
                    .h_full()
                    .border_r_1()
                    .border_color(theme::border())
                    .bg(theme::panel())
                    .child(self.rail_header())
                    .child(div().flex_1().child(self.cell_world(cx)))
                    .child(
                        div()
                            .border_t_1()
                            .border_color(theme::border())
                            .child(self.dynamics_feed()),
                    ),
            )
            // Center: inspector over blocklace.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .w(px(460.))
                    .h_full()
                    .border_r_1()
                    .border_color(theme::border())
                    .child(div().flex_1().child(self.inspector()))
                    .child(
                        div()
                            .h(px(260.))
                            .border_t_1()
                            .border_color(theme::border())
                            .bg(theme::panel())
                            .child(self.blocklace(cx)),
                    ),
            )
            // Right: the composer (drive the executor).
            .child(div().flex_1().h_full().child(self.composer(cx)))
    }
}

// --- small render helpers ---------------------------------------------------

fn sorted_cells(w: &World) -> Vec<CellId> {
    let mut ids: Vec<CellId> = w.ledger().iter().map(|(id, _)| *id).collect();
    ids.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    ids
}

fn kind_badge(kind: ObjectKind) -> impl IntoElement {
    let (label, color) = match kind {
        ObjectKind::Cell => ("cell", theme::accent()),
        ObjectKind::Receipt => ("receipt", theme::good()),
        ObjectKind::Capability => ("capability", theme::accent()),
        ObjectKind::Image => ("image", theme::warn()),
    };
    div().mb_2().child(pill(label, color))
}

fn field_row(f: &Field) -> impl IntoElement {
    let (val, color): (String, Hsla) = match &f.value {
        FieldValue::Text(s) => (s.clone(), theme::text()),
        FieldValue::Balance(b) => (
            b.to_string(),
            if *b < 0 { theme::warn() } else { theme::text() },
        ),
        FieldValue::Count(c) => (c.to_string(), theme::text()),
        FieldValue::Bool(b) => (
            b.to_string(),
            if *b { theme::good() } else { theme::muted() },
        ),
        FieldValue::Id(id) => (reflect::short_hex(id), theme::accent()),
        FieldValue::Hash(h) => (reflect::short_hex(h), theme::good()),
        FieldValue::CapEdge { target, slot } => {
            (format!("→ {} (slot {slot})", reflect::short_hex(target)), theme::accent())
        }
        FieldValue::FieldSlot { hex, .. } => (reflect::short_hex_hexstr(hex), theme::muted()),
    };
    div()
        .flex()
        .justify_between()
        .py_0p5()
        .child(div().text_xs().text_color(theme::muted()).child(f.key.clone()))
        .child(div().text_xs().text_color(color).child(val))
}

/// A verb button that runs a `&mut Cockpit` method through the listener.
fn verb_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    let id = SharedString::from(format!("verb-{label}"));
    div()
        .id(id)
        .px_3()
        .py_2()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
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
