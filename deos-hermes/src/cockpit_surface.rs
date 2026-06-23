//! THE AGENT DOCK COCKPIT SURFACE — mount the confined Hermes agent as a dock
//! pane in starbridge-v2.
//!
//! starbridge-v2's dock hosts any `CockpitSurface` (the slim ~8-method item
//! trait in `starbridge-v2/src/dock/surface.rs`). This module gives the confined
//! agent everything that trait needs, as a concrete [`HermesDockSurface`] handle
//! over a live [`AgentDockView`] gpui entity — rendering the agent's chat, the
//! tool-call ledger (each receipt / refusal), and the embedded mandate inspector.
//!
//! ## Two-file delivery (no starbridge-v2/cockpit touch)
//!
//! deos-hermes is its own workspace, so it can't `use` starbridge-v2's
//! `CockpitSurface` trait directly (that would invert the dependency). The split,
//! mirroring `deos_zed::cockpit_surface::EditorSurface` /
//! `deos_terminal::cockpit_surface::TerminalSurface`:
//!
//!   * **here** — [`HermesDockSurface`], a cloneable handle holding the
//!     [`AgentDockView`] entity, exposing `surface_id` / `tab_label` /
//!     `render_body` / `focus_handle` / `is_dirty` as plain INHERENT methods.
//!     This is the real, tested logic; the surface re-renders from the live
//!     [`AgentDockModel`] each frame.
//!   * **`starbridge-v2/src/dock/hermes_surface.rs`** (delivered ready-to-drop,
//!     see the impl-shell in this module's doc) — a ~25-line
//!     `impl CockpitSurface for HermesDockSurface` forwarding each trait method
//!     to the inherent method here. It lives in starbridge-v2 because that is
//!     where the trait lives; mounting it is a one-line `pub mod hermes_surface;`
//!     in `dock/mod.rs` (the dock module, NOT cockpit.rs) plus a `deos-hermes`
//!     path dependency.
//!
//! Because both crates pin the SAME gpui fork rev (see Cargo.toml), the
//! `Entity<AgentDockView>` here is byte-identical to the one starbridge-v2 sees —
//! the forward is a plain call, no glue.
//!
//! ## THE READY-TO-DROP MOUNT (the 2-edit note)
//!
//! ```text
//! // EDIT 1 — starbridge-v2/src/dock/hermes_surface.rs  (NEW, gpui is always
//! //          present in starbridge-v2; the dock module is gpui-side already)
//! use deos_hermes::cockpit_surface::HermesDockSurface;
//! use crate::dock::surface::{CockpitSurface, SurfaceId};
//! use gpui::{AnyElement, App, FocusHandle, SharedString, Window};
//!
//! impl CockpitSurface for HermesDockSurface {
//!     fn item_id(&self) -> SurfaceId { SurfaceId(self.surface_id()) }
//!     fn tab_label(&self) -> SharedString { self.tab_label() }
//!     fn render_body(&mut self, w: &mut Window, cx: &mut App) -> AnyElement {
//!         self.render_body(w, cx)
//!     }
//!     fn focus_handle(&self, cx: &App) -> FocusHandle { self.focus_handle(cx) }
//!     fn is_dirty(&self, cx: &App) -> bool { self.is_dirty(cx) }
//!     fn boxed_clone(&self) -> Box<dyn CockpitSurface> { Box::new(self.clone()) }
//! }
//!
//! // EDIT 2 — starbridge-v2/src/dock/mod.rs
//! pub mod hermes_surface;
//! ```
//!
//! Plus the path dependency in starbridge-v2/Cargo.toml:
//! `deos-hermes = { path = "../deos-hermes" }`. To CONSTRUCT one, the host opens a
//! [`HermesDockSurface::new`] with the session id + a starting [`AgentDockModel`],
//! and feeds it model updates from a background [`crate::AcpClient`] run (a
//! `update(model)` call per delta, or a re-derive from the accumulating
//! [`crate::PromptRun`] via [`AgentDockModel::from_run`]).

use gpui::{
    div, px, AnyElement, App, AppContext as _, Context, Entity, FocusHandle, Focusable,
    InteractiveElement as _, IntoElement, ParentElement as _, Render, SharedString, Styled as _,
    Window,
};
use gpui_component::{h_flex, v_flex};

use crate::surface::{AgentDockModel, ToolLine};

/// The live gpui view of a confined agent dock: it renders the chat pane, the
/// tool-call ledger, and the mandate inspector from its [`AgentDockModel`]. The
/// host pushes model updates ([`AgentDockView::set_model`]) as the agent's ACP
/// session streams; gpui re-renders on `cx.notify()`.
pub struct AgentDockView {
    model: AgentDockModel,
    focus: FocusHandle,
}

impl AgentDockView {
    /// Build the view over a starting model.
    pub fn new(model: AgentDockModel, cx: &mut Context<Self>) -> Self {
        Self {
            model,
            focus: cx.focus_handle(),
        }
    }

    /// Replace the model (a streamed delta or a re-derive from the running
    /// `PromptRun`) and request a repaint.
    pub fn set_model(&mut self, model: AgentDockModel, cx: &mut Context<Self>) {
        self.model = model;
        cx.notify();
    }

    /// The live model (host-side inspection).
    pub fn model(&self) -> &AgentDockModel {
        &self.model
    }

    // ── pane builders ──

    /// The chat pane: the agent's streamed message text + the terminal stop reason.
    fn chat_pane(&self) -> AnyElement {
        v_flex()
            .gap_1()
            .p_2()
            .child(div().text_color(HEADING).child("chat"))
            .child(
                div()
                    .text_color(BODY)
                    .child(SharedString::from(if self.model.agent_text.trim().is_empty() {
                        "(no agent output yet)".to_string()
                    } else {
                        self.model.agent_text.trim().to_string()
                    })),
            )
            .child(
                div()
                    .text_color(MUTED)
                    .text_size(px(12.))
                    .child(SharedString::from(format!("stop: {}", self.model.stop_reason))),
            )
            .into_any_element()
    }

    /// The tool-call ledger: one row per tool-call — ALLOW shows the receipt id +
    /// remaining budget (green ✓), REJECT shows the leg that bit (red ✗).
    fn ledger_pane(&self) -> AnyElement {
        let mut col = v_flex().gap_1().p_2().child(
            div()
                .text_color(HEADING)
                .child("tool-call ledger (receipts / refusals)"),
        );
        if self.model.tool_lines.is_empty() {
            col = col.child(div().text_color(MUTED).child("(no tool-calls yet)"));
        }
        for line in &self.model.tool_lines {
            col = col.child(self.ledger_row(line));
        }
        col.into_any_element()
    }

    fn ledger_row(&self, line: &ToolLine) -> AnyElement {
        let (mark, mark_color) = if line.allowed {
            ("✓", ALLOW)
        } else {
            ("✗", REJECT)
        };
        let rem = line
            .remaining
            .map(|r| format!("  [{r} left]"))
            .unwrap_or_default();
        h_flex()
            .gap_2()
            .child(div().text_color(mark_color).child(mark))
            .child(div().text_color(BODY).min_w(px(96.)).child(SharedString::from(line.name.clone())))
            .child(
                div()
                    .text_color(MUTED)
                    .text_size(px(12.))
                    .child(SharedString::from(line.tool_call_id.clone())),
            )
            .child(div().text_color(BODY).child(SharedString::from(format!("{}{}", line.detail, rem))))
            .into_any_element()
    }

    /// The mandate inspector pane — the agent's live confinement (grants /
    /// budgets / receipts), rendered from the model's pre-formatted text.
    fn mandate_pane(&self) -> AnyElement {
        let mut col = v_flex()
            .gap_1()
            .p_2()
            .child(div().text_color(HEADING).child("mandate inspector"));
        for ln in self.model.mandate_text.lines() {
            col = col.child(
                div()
                    .text_color(BODY)
                    .text_size(px(13.))
                    .child(SharedString::from(ln.to_string())),
            );
        }
        col.into_any_element()
    }
}

// A small, theme-independent palette so the surface paints without requiring a
// specific gpui-component Theme variant to be installed (the headless capture +
// the cockpit both work). Plain gpui Rgb literals.
const HEADING: gpui::Rgba = gpui::Rgba { r: 0.85, g: 0.90, b: 1.0, a: 1.0 };
const BODY: gpui::Rgba = gpui::Rgba { r: 0.82, g: 0.84, b: 0.88, a: 1.0 };
const MUTED: gpui::Rgba = gpui::Rgba { r: 0.55, g: 0.58, b: 0.64, a: 1.0 };
const ALLOW: gpui::Rgba = gpui::Rgba { r: 0.45, g: 0.85, b: 0.55, a: 1.0 };
const REJECT: gpui::Rgba = gpui::Rgba { r: 0.95, g: 0.45, b: 0.45, a: 1.0 };
const BG: gpui::Rgba = gpui::Rgba { r: 0.07, g: 0.08, b: 0.11, a: 1.0 };

impl Render for AgentDockView {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let _ = cx;
        v_flex()
            .key_context("HermesDock")
            .track_focus(&self.focus)
            .size_full()
            .bg(BG)
            .p_2()
            .gap_2()
            .child(
                div()
                    .text_color(HEADING)
                    .child(SharedString::from(format!(
                        "Hermes (confined) — session {}",
                        self.model.session_id
                    ))),
            )
            .child(self.chat_pane())
            .child(self.ledger_pane())
            .child(self.mandate_pane())
    }
}

impl Focusable for AgentDockView {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

/// A dock-mountable confined-agent surface: a stable id + the live
/// [`AgentDockView`] entity. Cheap to [`Clone`] (a handle + an id), so the dock's
/// `boxed_clone` on split is cheap. Hand this to starbridge-v2's
/// `impl CockpitSurface` (see the module doc's 2-edit mount note).
#[derive(Clone)]
pub struct HermesDockSurface {
    id: u64,
    view: Entity<AgentDockView>,
}

impl HermesDockSurface {
    /// Build a confined-agent surface over a starting [`AgentDockModel`]. `id` is
    /// the stable surface identity within a pane (the host supplies a monotonic
    /// counter or a `Tab` discriminant).
    pub fn new(id: u64, model: AgentDockModel, cx: &mut App) -> Self {
        let view = cx.new(|cx| AgentDockView::new(model, cx));
        Self { id, view }
    }

    /// Wrap an already-built view entity.
    pub fn from_view(id: u64, view: Entity<AgentDockView>) -> Self {
        Self { id, view }
    }

    /// The live view entity (host-side: push model updates as the ACP session
    /// streams, via `view.update(cx, |v, cx| v.set_model(m, cx))`).
    pub fn view(&self) -> &Entity<AgentDockView> {
        &self.view
    }

    /// Push a fresh model (a streamed delta or a `from_run` re-derive).
    pub fn set_model(&self, model: AgentDockModel, cx: &mut App) {
        self.view.update(cx, |v, cx| v.set_model(model, cx));
    }

    // --- the methods the host's `CockpitSurface` impl forwards to ------------

    /// `CockpitSurface::item_id` payload.
    pub fn surface_id(&self) -> u64 {
        self.id
    }

    /// `CockpitSurface::tab_label`.
    pub fn tab_label(&self) -> SharedString {
        SharedString::from("Hermes (confined)")
    }

    /// `CockpitSurface::focus_handle`.
    pub fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.view.read(cx).focus_handle(cx)
    }

    /// `CockpitSurface::render_body` — the live agent dock view.
    pub fn render_body(&mut self, _window: &mut Window, _cx: &mut App) -> AnyElement {
        div()
            .size_full()
            .child(self.view.clone())
            .into_any_element()
    }

    /// `CockpitSurface::is_dirty` — a confined agent is "dirty" (worth a marker)
    /// while its turn is in flight: the stop_reason not yet a terminal value.
    pub fn is_dirty(&self, cx: &App) -> bool {
        let sr = &self.view.read(cx).model().stop_reason;
        sr.is_empty()
    }
}
