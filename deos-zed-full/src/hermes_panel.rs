//! `hermes_panel` — the CONFINED-HERMES AGENT PANEL, docked into the real Zed
//! [`Workspace`].
//!
//! This is the seam that turns the embedded IDE into a live, receipted,
//! cap-confined agent dev-loop: a [`workspace::Panel`] that wraps deos-hermes's
//! live [`AgentDockView`](deos_hermes::cockpit_surface::AgentDockView) — the same
//! interactive surface the `agent_loop_acceptance` test drives — and `add_panel`s
//! it into the dock ALONGSIDE the project / outline / terminal panels.
//!
//! What makes it LIVE (not a snapshot): the wrapped view owns a real
//! [`HermesSession`](deos_hermes::cockpit_surface::HermesSession) — a persistent
//! [`HermesGateway`](deos_hermes::HermesGateway) over an embedded cipherclerk + the
//! verified Lean executor. Driving the agent (a typed prompt → the in-process ACP
//! peer → the gate) fires REAL cap-gated, metered, receipted dregg turns; the
//! panel's ledger + budget bars repaint from the same [`AgentDockModel`] the gate
//! mutates. Budgets deplete; an out-of-mandate call is refused in-band, naming the
//! leg that bit. The agent's *brain* is the faithful scripted/mock ACP peer (the
//! live model is environment-blocked, per deos-hermes's honest scope); the gate,
//! executor, receipts, and ACP wire are all real.
//!
//! Because the wrapped view is a gpui `Entity` on the SAME zed-fork gpui this
//! crate's Workspace uses, the panel drops straight into the dock — no second gpui
//! linkage, no bridging. The panel is `Panel: Focusable + EventEmitter<PanelEvent>
//! + Render`; it forwards focus + render to the embedded Hermes view.
//!
//! Only built under `--features full-zed` (it needs the heavy Zed graph + the
//! deos-hermes `cockpit-surface`).
#![cfg(feature = "full-zed")]

use gpui::{
    App, AppContext as _, Context, Entity, EventEmitter, FocusHandle, Focusable,
    InteractiveElement as _, IntoElement, ParentElement as _, Pixels, Render, Styled as _, Window,
    actions,
};
use ui::IconName;
use workspace::Workspace;
use workspace::dock::{DockPosition, Panel, PanelEvent};

pub use deos_hermes::cockpit_surface::{AgentDockView, HermesSession};
pub use deos_hermes::surface::AgentDockModel;

actions!(
    hermes_panel,
    [
        /// Focus the confined-Hermes agent panel.
        ToggleFocus
    ]
);

/// Where the agent panel docks. Right is the conventional "assistant/agent
/// sidebar" position (Zed's own agent panel docks right too).
const PERSISTENT_NAME: &str = "Hermes Agent Panel";
const PANEL_KEY: &str = "HermesAgentPanel";

/// The confined-Hermes agent panel: a [`workspace::Panel`] wrapping the live
/// deos-hermes [`AgentDockView`]. The view holds the real, persistent
/// [`HermesGateway`]; this panel is the dock-citizen shell around it.
pub struct HermesPanel {
    /// The live agent-dock view (owns the confined `HermesSession` + the
    /// `AgentDockModel` the ledger/budget panes render).
    view: Entity<AgentDockView>,
    /// The panel's own focus handle; focusing the panel focuses the agent view's
    /// prompt input.
    focus: FocusHandle,
    /// The dock side (left/right) this panel sits on.
    position: DockPosition,
}

impl HermesPanel {
    /// Build the panel over an EXPLICIT, host-built [`AgentDockView`] (the common
    /// case for a host that wants a specific confinement — see
    /// [`HermesSession::with_gateway`]).
    pub fn from_view(view: Entity<AgentDockView>, cx: &mut Context<Self>) -> Self {
        Self {
            view,
            focus: cx.focus_handle(),
            position: DockPosition::Right,
        }
    }

    /// Build the panel over a fresh INTERACTIVE confined session (the standard
    /// deos confinement: per-kind floors + the curated per-tool tightenings). The
    /// view is constructed on this panel's gpui context.
    pub fn new_interactive(session_id: &str, window: &mut Window, cx: &mut Context<Self>) -> Self {
        let model = AgentDockModel::new_live(session_id);
        let view = cx.new(|cx| AgentDockView::new(model, window, cx));
        Self::from_view(view, cx)
    }

    /// Build the panel over a caller-provided confined [`HermesSession`] — the
    /// path a host uses to install a SPECIFIC mandate (a tighter terminal rate, a
    /// whole-tool deny) instead of the standard floors. The starting model is a
    /// fresh live one for the session id.
    pub fn over_session(
        session: HermesSession,
        session_id: &str,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> Self {
        let model = AgentDockModel::new_live(session_id);
        let view = cx.new(|cx| AgentDockView::with_session(model, session, window, cx));
        Self::from_view(view, cx)
    }

    /// The live agent-dock view entity (host-side inspection / driving).
    pub fn view(&self) -> &Entity<AgentDockView> {
        &self.view
    }
}

impl Focusable for HermesPanel {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl EventEmitter<PanelEvent> for HermesPanel {}

impl Render for HermesPanel {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
        // The panel body IS the live Hermes agent dock view — focus-tracked so
        // focusing the panel routes to the agent's prompt input.
        gpui::div()
            .track_focus(&self.focus)
            .size_full()
            .child(self.view.clone())
    }
}

impl Panel for HermesPanel {
    fn persistent_name() -> &'static str {
        PERSISTENT_NAME
    }

    fn panel_key() -> &'static str {
        PANEL_KEY
    }

    fn position(&self, _window: &Window, _cx: &App) -> DockPosition {
        self.position
    }

    fn position_is_valid(&self, position: DockPosition) -> bool {
        matches!(position, DockPosition::Left | DockPosition::Right)
    }

    fn set_position(
        &mut self,
        position: DockPosition,
        _window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        // Bottom is not a valid dock for an agent sidebar; clamp to left/right.
        self.position = match position {
            DockPosition::Bottom => DockPosition::Right,
            other => other,
        };
        cx.notify();
    }

    fn default_size(&self, _window: &Window, _cx: &App) -> Pixels {
        gpui::px(420.)
    }

    fn icon(&self, _window: &Window, _cx: &App) -> Option<IconName> {
        Some(IconName::ZedAssistant)
    }

    fn icon_tooltip(&self, _window: &Window, _cx: &App) -> Option<&'static str> {
        Some("Hermes (confined agent)")
    }

    fn toggle_action(&self) -> Box<dyn gpui::Action> {
        Box::new(ToggleFocus)
    }

    fn activation_priority(&self) -> u32 {
        // After the project panel (1); a low priority keeps it from stealing the
        // default-open slot.
        4
    }

    /// This IS deos's agent panel — mark it so the workspace treats it as the
    /// agent surface (the dock's agent affordances key off this).
    fn is_agent_panel(&self) -> bool {
        true
    }
}

/// Build a [`HermesPanel`] over `session` and `add_panel` it into `workspace`'s
/// dock — the same `Panel::load`→`add_panel` dance `boot::load_firmament_panels`
/// runs for the project/outline/terminal panels, for the agent panel. Returns the
/// docked panel entity (resolvable afterward via `workspace.panel::<HermesPanel>()`).
pub fn add_hermes_panel(
    workspace: &mut Workspace,
    session: HermesSession,
    session_id: &str,
    window: &mut Window,
    cx: &mut Context<Workspace>,
) -> Entity<HermesPanel> {
    let panel = cx.new(|cx| HermesPanel::over_session(session, session_id, window, cx));
    workspace.add_panel(panel.clone(), window, cx);
    panel
}
