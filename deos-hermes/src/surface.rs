//! THE CONFINED-AGENT DOCK SURFACE — a ready-to-mount sketch (no starbridge-v2 dep).
//!
//! This module is the DESIGN + a compiling data-model sketch for surfacing the
//! confined Hermes as a deos agent dock: a `CockpitSurface` (the starbridge-v2
//! moldable-inspector seam) that streams Hermes's `session/update` output, shows
//! each tool-call's receipt/refusal live, and embeds the [`crate::mandate`]
//! inspector. It deliberately does NOT depend on `gpui` / starbridge-v2 (that
//! crate is its own standalone workspace, and this one must build with only the
//! SDK). What lives here is (a) the dock's VIEW-MODEL — a plain struct the dock
//! renders from, kept in lock-step with a running [`crate::AcpClient`] — and (b)
//! the mounting recipe, as the module doc, so wiring it into starbridge-v2 is a
//! mechanical lift, not a redesign.
//!
//! # The two confinement faces (defense in depth)
//!
//! A confined Hermes agent has TWO independent confinement faces, and the dock
//! surfaces both:
//!
//! 1. **The authority face — the [`crate::HermesGateway`].** Every tool-call is a
//!    cap-gated, metered, receipted dregg turn (or an in-band refusal). This is
//!    the face this crate fully implements: the gate proves the call was
//!    authorized under deos's mandate, and the receipt witnesses it.
//!
//! 2. **The ambient-authority face — the sandbox host-PD (firmament/seL4).** The
//!    Hermes process runs in a confined protection-domain (the host-PD the
//!    firmament work boots — `project-firmament-sel4-boots`): its filesystem is a
//!    cap-scoped VFS (`FirmamentFs`), its network an explicit net-cap. Even if a
//!    tool-call slipped the gate, the PD physically cannot reach anything outside
//!    its caps. The gate is the *intent* authority; the PD is the *ambient*
//!    authority — neither alone is the whole confinement.
//!
//! `deos-hermes` owns face (1). Face (2) is the firmament seam: the recipe below
//! says exactly how the dock launches Hermes INTO a sandbox host-PD rather than
//! as a bare `Command`.
//!
//! # Mounting recipe (the ready-to-mount lift into starbridge-v2)
//!
//! In `starbridge-v2`, behind its `gpui-ui` cfg (so the `--lib` suite stays
//! gpui-free — see the "Cockpit Edits Need the gpui Build Check" practice):
//!
//! ```text
//! // starbridge-v2/src/dock/hermes_surface.rs  (NEW, gpui-gated)
//! use deos_hermes::{AcpClient, MockHermesPeer /* or AcpTransport */, HermesGateway,
//!                   GrantRegistry, Mandate};
//! use deos_hermes::surface::AgentDockModel;
//! use crate::dock::surface::{CockpitSurface, SurfaceId};
//!
//! pub struct HermesDockSurface {
//!     id: SurfaceId,
//!     model: AgentDockModel,          // ← the view-model from THIS module
//!     // a background thread runs `AcpClient::run_prompt`, pushing PromptRun
//!     // deltas into `model` via a channel; render_body reads `model`.
//! }
//!
//! impl CockpitSurface for HermesDockSurface {
//!     fn item_id(&self) -> SurfaceId { self.id }
//!     fn tab_label(&self) -> SharedString { "Hermes (confined)".into() }
//!     fn render_body(&mut self, _w, cx) -> AnyElement {
//!         // 1. a chat pane: model.agent_text (streamed agent_message_chunks)
//!         // 2. a tool-call ledger: model.tool_lines — each ALLOW shows the
//!         //    receipt id + remaining budget; each REJECT shows the leg that bit
//!         // 3. the mandate inspector: render model.mandate_text (Mandate::render_text)
//!         div().child(self.chat(cx)).child(self.ledger(cx)).child(self.mandate(cx)).into_any()
//!     }
//!     // …focus_handle / boxed_clone per the trait.
//! }
//! ```
//!
//! ## Launching Hermes INTO a sandbox host-PD (face 2) — NOW REAL
//!
//! [`crate::AcpTransport::spawn_hermes`] spawns a bare `Command` (no ambient
//! confinement). The sandbox lift is implemented in [`crate::confined`]:
//! [`spawn_hermes_in_pd`](crate::confined::spawn_hermes_in_pd) forks an
//! OS-sandboxed firmament host-PD (`spawn_pd_confined` — macOS Seatbelt / Linux
//! ns+seccomp+landlock) and runs the agent inside it, reachable ONLY over its
//! firmament Endpoint. The `AcpClient` driver is UNCHANGED: it speaks ndjson over
//! [`PdAcpTransport`](crate::confined::PdAcpTransport) (the Endpoint) exactly as
//! it does over the in-process mock; the difference is purely WHERE the peer
//! runs, and that it now runs with NO ambient OS authority.
//!
//! HONEST SCOPE: the confined child has no exec authority (the sandbox's whole
//! point), so the agent body is a Rust ACP STAND-IN (the live `hermes acp` venv
//! is broken here anyway), not an `execve`'d external binary. The confinement and
//! the ACP wire are real; what is stood-in is the agent's brain. The cwd-cap /
//! net-cap of the seam map to a `Confinement::with_read_path` + a passed socket
//! fd (the next slice past Endpoint-only). See [`crate::confined`].
//!
//! This module's [`AgentDockModel`] is the bridge between the running client and
//! whatever renders it — usable from the gpui dock, a TUI, or a test.

use crate::acp::PermissionOutcome;
use crate::acp_client::PromptRun;
use crate::bridge::HermesGateway;
use crate::mandate::Mandate;

/// One rendered tool-call line for the dock's tool-call ledger.
#[derive(Clone, Debug)]
pub struct ToolLine {
    /// The ACP tool-call id.
    pub tool_call_id: String,
    /// The Hermes tool name.
    pub name: String,
    /// `true` if allowed (a receipted turn), `false` if refused in-band.
    pub allowed: bool,
    /// The receipt id (turn hash, hex) on an allow, or the refusal reason on a reject.
    pub detail: String,
    /// Calls remaining on this tool's mandate after this call (allows only).
    pub remaining: Option<i64>,
}

/// The dock's VIEW-MODEL: everything a `CockpitSurface` renders for a confined
/// Hermes session. A plain struct (no gpui), updated from a [`PromptRun`] +
/// the live [`HermesGateway`], so the dock, a TUI, or a test all render the same.
#[derive(Clone, Debug, Default)]
pub struct AgentDockModel {
    /// The session this dock confines.
    pub session_id: String,
    /// The streamed agent message text (the chat pane body).
    pub agent_text: String,
    /// One line per tool-call (the tool-call ledger).
    pub tool_lines: Vec<ToolLine>,
    /// The rendered mandate inspector text (grants / budgets / receipts).
    pub mandate_text: String,
    /// The prompt's terminal `stop_reason`.
    pub stop_reason: String,
}

impl AgentDockModel {
    /// Build the dock model from a finished [`PromptRun`] and the live gateway it
    /// was driven through. Call after `AcpClient::run_prompt` returns (or
    /// incrementally, re-deriving from the accumulating run for a live dock).
    pub fn from_run<'rt>(
        session_id: &str,
        run: &PromptRun,
        gateway: &HermesGateway<'rt>,
    ) -> AgentDockModel {
        let tool_lines = run
            .verdicts
            .iter()
            .map(|(call, outcome)| match outcome {
                PermissionOutcome::Allow {
                    tool_call_id,
                    receipt,
                    remaining,
                } => ToolLine {
                    tool_call_id: tool_call_id.clone(),
                    name: call.name.clone(),
                    allowed: true,
                    detail: format!("receipt {}…", &receipt[..16.min(receipt.len())]),
                    remaining: Some(*remaining),
                },
                PermissionOutcome::Reject {
                    tool_call_id,
                    reason,
                } => ToolLine {
                    tool_call_id: tool_call_id.clone(),
                    name: call.name.clone(),
                    allowed: false,
                    detail: reason.clone(),
                    remaining: None,
                },
            })
            .collect();

        let mandate = Mandate::from_session(session_id, gateway, &run.verdicts);

        AgentDockModel {
            session_id: session_id.to_string(),
            agent_text: run.agent_text.clone(),
            tool_lines,
            mandate_text: mandate.render_text(),
            stop_reason: run.stop_reason.clone(),
        }
    }

    /// A plain-text rendering of the whole dock (for a CLI / TUI / a test). The
    /// gpui dock renders the same fields as styled panes instead.
    pub fn render_text(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("╭─ Hermes (confined) — session {}\n", self.session_id));
        s.push_str(&format!("│ chat: {}\n", self.agent_text.trim()));
        s.push_str("│ tool-calls:\n");
        for line in &self.tool_lines {
            let mark = if line.allowed { "✓" } else { "✗" };
            let rem = line
                .remaining
                .map(|r| format!(" [{r} left]"))
                .unwrap_or_default();
            s.push_str(&format!(
                "│   {mark} {:<12} {} {}{}\n",
                line.name, line.tool_call_id, line.detail, rem
            ));
        }
        s.push_str(&format!("│ stop: {}\n", self.stop_reason));
        s.push_str("├─ ");
        s.push_str(&self.mandate_text.replace('\n', "\n│  "));
        s.push_str("\n╰─\n");
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acp::ToolCallRequest;
    use crate::grant_registry::GrantRegistry;
    use crate::HermesGateway;
    use dregg_sdk::{AgentCipherclerk, AgentRuntime};
    use std::sync::{Arc, RwLock};

    #[test]
    fn dock_model_renders_chat_ledger_and_mandate() {
        let mut cclerk = AgentCipherclerk::new();
        let root = cclerk.mint_token(&[7u8; 32], "deos");
        let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
        let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
        let mut gw = HermesGateway::new(&rt, root, registry);

        let mut run = PromptRun {
            agent_text: "working…".into(),
            stop_reason: "end_turn".into(),
            ..Default::default()
        };
        let call = ToolCallRequest::new("s1", "tc-1", "web_search", serde_json::json!({"query":"x"}));
        let outcome = gw.admit_call(&call, 50);
        run.verdicts.push((call, outcome));

        let model = AgentDockModel::from_run("s1", &run, &gw);
        assert_eq!(model.tool_lines.len(), 1);
        assert!(model.tool_lines[0].allowed);
        let text = model.render_text();
        assert!(text.contains("Hermes (confined)"));
        assert!(text.contains("web_search"));
        assert!(text.contains("MANDATE"));
    }
}
