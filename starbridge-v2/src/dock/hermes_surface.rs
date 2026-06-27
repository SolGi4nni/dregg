//! Mount the CONFINED HERMES AGENT as a [`CockpitSurface`] — the ADOS dev-loop
//! made visible: a chat pane, the tool-call ledger (every tool-call a cap-gated,
//! RECEIPTED turn — or an in-band refusal), and the live mandate inspector.
//!
//! READY-TO-DROP, mirroring [`super::terminal_surface`] / [`super::editor_surface`]:
//! this file forwards the cockpit's [`CockpitSurface`] trait to the inherent
//! methods on [`deos_hermes::cockpit_surface::HermesDockSurface`] (the real,
//! tested surface logic lives in deos-hermes; the trait lives here, so this is
//! where the `impl` must live). Mounting is two edits, both in the dock module
//! (NOT `cockpit.rs`):
//!
//!   1. Add to `starbridge-v2/Cargo.toml` (a cross-workspace path dep is fine —
//!      deos-hermes pins the SAME gpui fork @407a6ff, so one gpui resolves):
//!
//!      ```toml
//!      deos-hermes = { path = "../deos-hermes", features = ["cockpit-surface"], optional = true }
//!      ```
//!
//!   2. Add `pub mod hermes_surface;` to `starbridge-v2/src/dock/mod.rs` (under
//!      the `dev-surfaces` feature, like the editor + terminal surfaces).
//!
//! Then the cockpit opens one on-demand (`open_agent_pane`) into its own split
//! pane, like the terminal/editor dev panes.
//!
//! The surface renders from a plain [`deos_hermes::surface::AgentDockModel`] (a
//! gpui-free view-model). [`AgentPane::demo`] seeds a self-contained model — a
//! real [`HermesGateway`] over the embedded cipherclerk admitting a couple of
//! tool-calls (one allowed-and-receipted, one refused) plus the rendered mandate
//! — so the pane RENDERS the whole ledger + inspector without a live ACP session
//! attached. A host driving a live agent pushes deltas via `surface.set_model`.

use deos_hermes::cockpit_surface::HermesDockSurface;
use deos_hermes::surface::AgentDockModel;
use gpui::{AnyElement, App, FocusHandle, SharedString, Window};

use super::surface::{CockpitSurface, SurfaceId};

/// A dock-hostable wrapper around a deos-hermes agent surface.
#[derive(Clone)]
pub struct AgentPane(HermesDockSurface);

impl AgentPane {
    /// Build an agent pane over a starting [`AgentDockModel`].
    pub fn new(id: u64, model: AgentDockModel, window: &mut Window, cx: &mut App) -> Self {
        AgentPane(HermesDockSurface::new(id, model, window, cx))
    }

    /// Build an INTERACTIVE agent pane: a live, typed-prompt → streamed-reply
    /// agent chat over a persistent [`HermesGateway`] (every tool-call a cap-gated
    /// receipted turn, budgets depleting turn-over-turn). This is what ⌘K → "Open
    /// Agent pane" gives — the real ADOS sidebar, not a snapshot.
    pub fn interactive(id: u64, session_id: &str, window: &mut Window, cx: &mut App) -> Self {
        AgentPane(HermesDockSurface::new_interactive(
            id, session_id, window, cx,
        ))
    }

    /// Build a DEMO agent pane: seed a self-contained [`AgentDockModel`] from a
    /// real [`HermesGateway`] over the embedded cipherclerk, admitting a couple
    /// of tool-calls (one ALLOWED + receipted, one REFUSED) so the ledger + the
    /// mandate inspector render without a live ACP session attached. Used by the
    /// headless showcase bake. The gateway is local to this call — the produced
    /// `AgentDockModel` is a plain (gpui-free, `Clone`) struct, so nothing of the
    /// runtime lifetime escapes.
    pub fn demo(id: u64, window: &mut Window, cx: &mut App) -> Self {
        AgentPane::new(id, demo_model(), window, cx)
    }

    /// The underlying surface handle (host-side: push live-session model deltas
    /// via `pane.surface().set_model(model, cx)` as the ACP session streams).
    pub fn surface(&self) -> &HermesDockSurface {
        &self.0
    }
}

impl CockpitSurface for AgentPane {
    fn item_id(&self) -> SurfaceId {
        SurfaceId(self.0.surface_id())
    }

    fn tab_label(&self) -> SharedString {
        self.0.tab_label()
    }

    fn render_body(&mut self, window: &mut Window, cx: &mut App) -> AnyElement {
        self.0.render_body(window, cx)
    }

    fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.0.focus_handle(cx)
    }

    fn is_dirty(&self, cx: &App) -> bool {
        self.0.is_dirty(cx)
    }

    fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
        Box::new(self.clone())
    }
}

/// Build the demo dock model: a real confined-Hermes session admitting two
/// tool-calls through the proven [`HermesGateway`] — `web_search` (ALLOWED, a
/// receipted turn) and a deliberately over-budget `write_file` (REFUSED) — so
/// the rendered ledger shows BOTH the receipt and the refusal, and the mandate
/// inspector shows the live confinement. Mirrors the deos-hermes
/// `dock_model_renders_chat_ledger_and_mandate` test.
fn demo_model() -> AgentDockModel {
    use deos_hermes::acp::ToolCallRequest;
    use deos_hermes::grant_registry::GrantRegistry;
    use deos_hermes::HermesGateway;
    use dregg_sdk::{AgentCipherclerk, AgentRuntime};
    use std::sync::{Arc, RwLock};

    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    let registry = GrantRegistry::default_for_session(1_000).with_standard_tool_grants(1_000);
    let mut gw = HermesGateway::new(&rt, root, registry);

    let session = "deos-demo";
    let mut run = deos_hermes::PromptRun {
        agent_text: "Searched the web, then tried to write outside my mandate.".into(),
        stop_reason: "end_turn".into(),
        ..Default::default()
    };

    // ALLOWED — an in-mandate web_search: a real cap-gated, receipted turn.
    let allowed = ToolCallRequest::new(
        session,
        "tc-1",
        "web_search",
        serde_json::json!({ "query": "ocap capability security" }),
    );
    let outcome = gw.admit_call(&allowed, 50);
    run.verdicts.push((allowed, outcome));

    // REFUSED — an over-budget / out-of-mandate write: the gate REFUSES in-band
    // (the leg that bit is shown in the ledger).
    let refused = ToolCallRequest::new(
        session,
        "tc-2",
        "write_file",
        serde_json::json!({ "path": "/etc/passwd", "contents": "x" }),
    );
    // Past the registry deadline → the deadline caveat refuses (fail-closed).
    let outcome = gw.admit_call(&refused, 10_000);
    run.verdicts.push((refused, outcome));

    AgentDockModel::from_run(session, &run, &gw)
}
