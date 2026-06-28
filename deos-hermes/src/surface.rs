//! THE CONFINED-AGENT DOCK VIEW-MODEL — the live, multi-turn model the gpui dock
//! paints (no gpui / starbridge-v2 dep).
//!
//! This module is the gpui-free VIEW-MODEL for the confined-agent dock: the live
//! [`AgentDockModel`] the gpui [`crate::cockpit_surface::AgentDockView`] renders
//! from. It is a real interactive-chat model, not a post-hoc snapshot:
//!
//!   * a multi-turn [`ChatEntry`] transcript — user prompts + streamed agent
//!     replies + the gated tool-calls inline, accumulating across turns;
//!   * the prominent [`PermissionMoment`] — the most recent gate decision
//!     (allow→receipt+budget / refuse→the [`RefusalLeg`] that bit);
//!   * the live [`MandateBudget`] rows whose bars deplete as the agent spends.
//!
//! It is driven INCREMENTALLY: [`AgentDockModel::push_user_prompt`] opens a turn
//! and [`AgentDockModel::apply_event`] folds each [`crate::StreamEvent`] from a
//! running [`crate::AcpClient::run_prompt_streaming`] as it arrives — so the dock
//! repaints token-by-token. ([`AgentDockModel::from_run`] still builds a one-shot
//! model from a finished `PromptRun` for the CLI / a test.) It depends only on the
//! SDK; the gpui view + the live session driver live in
//! [`crate::cockpit_surface`].
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
//! `deos-hermes` owns face (1). Face (2) is the firmament seam: the note below
//! says exactly how the dock launches Hermes INTO a sandbox host-PD rather than
//! as a bare `Command`.
//!
//! # The interactive dock (the gpui view)
//!
//! The live gpui surface that paints this model — the prompt input box, the
//! token-streaming transcript, the prominent permission moment, and the depleting
//! budget bars — is [`crate::cockpit_surface::AgentDockView`] /
//! [`crate::cockpit_surface::HermesDockSurface`] (the `cockpit-surface` feature).
//! Mounting it in starbridge-v2 is the 2-edit `CockpitSurface` forward documented
//! there. This module is just the gpui-free model it renders from.
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

use crate::acp::{PermissionOutcome, ToolCallRequest, ToolKind};
use crate::acp_client::{PromptRun, StreamEvent};
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

/// The leg of the mandate that a refusal bit — extracted from the gateway's
/// refusal text so the permission moment can name it crisply.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefusalLeg {
    /// The presented tool was out of the worker's scope.
    Scope,
    /// The mandate window's rate ceiling was exhausted.
    Rate,
    /// The call arrived past the mandate deadline.
    Deadline,
    /// An executor / admission error (not one of the three mandate legs).
    Other,
}

impl RefusalLeg {
    /// Classify a gateway refusal reason string into its leg.
    pub fn classify(reason: &str) -> RefusalLeg {
        if reason.contains("out of scope") {
            RefusalLeg::Scope
        } else if reason.contains("rate exhausted") {
            RefusalLeg::Rate
        } else if reason.contains("past deadline") {
            RefusalLeg::Deadline
        } else {
            RefusalLeg::Other
        }
    }

    /// A short label for the permission panel.
    pub fn label(self) -> &'static str {
        match self {
            RefusalLeg::Scope => "scope",
            RefusalLeg::Rate => "rate",
            RefusalLeg::Deadline => "deadline",
            RefusalLeg::Other => "error",
        }
    }
}

/// One entry in the multi-turn chat transcript. A confined-agent conversation is
/// an interleaving of the human's prompts, the agent's streamed replies, and the
/// gated tool-calls inline where the agent reached for them.
#[derive(Clone, Debug)]
pub enum ChatEntry {
    /// A prompt the human typed and sent.
    User { text: String },
    /// The agent's streamed reply text (grows chunk-by-chunk while live).
    Agent { text: String },
    /// A gated tool-call, inline in the transcript where the agent made it.
    Tool { line: ToolLine },
}

/// The most recent permission decision, surfaced prominently as "the permission
/// moment" — the human SEES every agent reach gated in real time.
#[derive(Clone, Debug)]
pub struct PermissionMoment {
    /// The Hermes tool name reached for.
    pub tool: String,
    /// The mandate the call was gated under (e.g. `tool:terminal` / `kind:Fetch`).
    pub mandate: String,
    /// `true` = allowed (a receipted turn), `false` = refused in-band.
    pub allowed: bool,
    /// On allow: the receipt id (hex turn hash). On reject: the refusal reason.
    pub detail: String,
    /// On allow: calls remaining on the mandate after this one.
    pub remaining: Option<i64>,
    /// On reject: which leg of the mandate bit.
    pub leg: Option<RefusalLeg>,
}

/// The dock's VIEW-MODEL: everything a `CockpitSurface` renders for a confined
/// Hermes session. A plain struct (no gpui), updated from a [`PromptRun`] +
/// the live [`HermesGateway`], so the dock, a TUI, or a test all render the same.
#[derive(Clone, Debug, Default)]
pub struct AgentDockModel {
    /// The session this dock confines.
    pub session_id: String,
    /// The streamed agent message text of the CURRENT turn (the chat pane body
    /// for the in-flight reply; the multi-turn record lives in `transcript`).
    pub agent_text: String,
    /// One line per tool-call (the flat tool-call ledger — every gated call this
    /// session, across all turns).
    pub tool_lines: Vec<ToolLine>,
    /// The rendered mandate inspector text (grants / budgets / receipts).
    pub mandate_text: String,
    /// The prompt's terminal `stop_reason` (empty while a turn is in flight).
    pub stop_reason: String,

    // ── the LIVE, multi-turn additions ──
    /// The multi-turn conversation: user prompts, agent replies, inline gated
    /// tool-calls — accumulating across turns.
    pub transcript: Vec<ChatEntry>,
    /// The most recent gate decision, surfaced as the prominent permission moment.
    pub last_permission: Option<PermissionMoment>,
    /// The structured live mandate (rows with budgets), kept alongside the
    /// pre-rendered `mandate_text` so the dock can paint depleting budget bars.
    pub mandate_rows: Vec<MandateBudget>,
    /// `true` while a turn is being driven (the agent is "thinking"/streaming).
    pub running: bool,
    /// A short status banner (e.g. "waiting for your prompt", "streaming…").
    pub status: String,
}

/// One mandate's live budget for the depleting-budget view: name, ceiling, spent.
#[derive(Clone, Debug)]
pub struct MandateBudget {
    /// The mandate label (e.g. `tool:terminal`, `kind:Fetch`).
    pub label: String,
    /// The granted rate ceiling.
    pub rate_limit: i64,
    /// Calls committed against this mandate so far this session.
    pub spent: i64,
    /// `true` if deos pinned a tighter per-tool grant (vs a kind floor).
    pub per_tool: bool,
}

impl MandateBudget {
    /// Remaining budget (clamped at 0).
    pub fn remaining(&self) -> i64 {
        (self.rate_limit - self.spent).max(0)
    }
    /// Spent fraction in `0.0..=1.0` for a budget bar.
    pub fn fraction_spent(&self) -> f32 {
        if self.rate_limit <= 0 {
            return 1.0;
        }
        (self.spent as f32 / self.rate_limit as f32).clamp(0.0, 1.0)
    }
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
            .map(|(call, outcome)| tool_line_from(call, outcome))
            .collect();

        let mandate = Mandate::from_session(session_id, gateway, &run.verdicts);

        AgentDockModel {
            session_id: session_id.to_string(),
            agent_text: run.agent_text.clone(),
            tool_lines,
            mandate_text: mandate.render_text(),
            stop_reason: run.stop_reason.clone(),
            transcript: Vec::new(),
            last_permission: None,
            mandate_rows: budget_rows(&mandate),
            running: false,
            status: String::new(),
        }
    }

    /// A fresh, empty live model for an interactive session — the dock starts
    /// here and grows it turn-by-turn via [`AgentDockModel::push_user_prompt`] +
    /// [`AgentDockModel::apply_event`].
    pub fn new_live(session_id: &str) -> AgentDockModel {
        AgentDockModel {
            session_id: session_id.to_string(),
            status: "type a prompt to the confined agent and press Enter".into(),
            ..Default::default()
        }
    }

    // ── the LIVE, incremental mutators (the interactive dock drives these) ──

    /// Record a prompt the human just submitted: append it to the transcript,
    /// open a fresh agent reply slot, and flip into the running state.
    pub fn push_user_prompt(&mut self, prompt: &str) {
        self.transcript.push(ChatEntry::User {
            text: prompt.to_string(),
        });
        self.agent_text.clear();
        self.stop_reason.clear();
        self.running = true;
        self.status = "streaming…".into();
    }

    /// Apply one live [`StreamEvent`] from the driven prompt, mutating the model
    /// the dock paints. Streaming = these arrive one at a time; the dock repaints
    /// after each, so text streams in chunk-by-chunk and tool-calls appear live.
    ///
    /// `mandate` is the freshly-derived live mandate (budgets after the gate
    /// decided), so the budget visibly depletes per allowed tool-call. Pass the
    /// current [`Mandate`] (cheap to rebuild from the gateway after each verdict).
    pub fn apply_event(&mut self, event: &StreamEvent, mandate: Option<&Mandate>) {
        match event {
            StreamEvent::SessionStarted { session_id } => {
                self.session_id = session_id.clone();
            }
            StreamEvent::AgentChunk { text } => {
                // Stream into the live agent reply: append to the current text and
                // to the trailing Agent transcript entry (create one if needed).
                self.agent_text.push_str(text);
                match self.transcript.last_mut() {
                    Some(ChatEntry::Agent { text: t }) => t.push_str(text),
                    _ => self
                        .transcript
                        .push(ChatEntry::Agent { text: text.clone() }),
                }
            }
            StreamEvent::ToolCall { call } => {
                // The agent reached for a tool — surface it in-flight (pending),
                // before the gate has decided. The verdict (next event) updates it.
                self.status = format!("gating {}…", call.name);
            }
            StreamEvent::Verdict { call, outcome } => {
                let line = tool_line_from(call, outcome);
                self.last_permission = Some(permission_moment(call, outcome, &line));
                self.transcript.push(ChatEntry::Tool { line: line.clone() });
                self.tool_lines.push(line);
                if let Some(m) = mandate {
                    self.mandate_text = m.render_text();
                    self.mandate_rows = budget_rows(m);
                }
            }
            StreamEvent::Stopped { stop_reason } => {
                self.stop_reason = stop_reason.clone();
                self.running = false;
                self.status = "idle — ask another question".into();
                if let Some(m) = mandate {
                    self.mandate_text = m.render_text();
                    self.mandate_rows = budget_rows(m);
                }
            }
        }
    }

    /// Record a transport error against the running turn (so a dead session shows
    /// a banner instead of silently hanging).
    pub fn fail(&mut self, reason: &str) {
        self.running = false;
        self.stop_reason = "error".into();
        self.status = format!("session error: {reason}");
    }

    /// A plain-text rendering of the whole dock (for a CLI / TUI / a test). The
    /// gpui dock renders the same fields as styled panes instead.
    pub fn render_text(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!(
            "╭─ Hermes (confined) — session {}\n",
            self.session_id
        ));
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

/// Render a [`ToolLine`] from a tool-call + its gateway verdict (shared by
/// `from_run` and the live `apply_event`).
pub(crate) fn tool_line_from(call: &ToolCallRequest, outcome: &PermissionOutcome) -> ToolLine {
    match outcome {
        PermissionOutcome::Allow {
            tool_call_id,
            receipt,
            remaining,
            ..
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
    }
}

/// Build the prominent [`PermissionMoment`] from a verdict: which tool, which
/// mandate it gated under, allow+receipt+budget or reject+leg.
fn permission_moment(
    call: &ToolCallRequest,
    outcome: &PermissionOutcome,
    line: &ToolLine,
) -> PermissionMoment {
    // The mandate label mirrors the gateway's tightest-wins routing: a per-tool
    // grant for the curated dangerous tools, else the kind floor.
    let mandate = match call.name.as_str() {
        "terminal" | "write_file" | "patch" | "web_extract" | "delegate_task" => {
            format!("tool:{}", call.name)
        }
        _ => format!("kind:{:?}", ToolKind::of_tool(&call.name)),
    };
    match outcome {
        PermissionOutcome::Allow { remaining, .. } => PermissionMoment {
            tool: call.name.clone(),
            mandate,
            allowed: true,
            detail: line.detail.clone(),
            remaining: Some(*remaining),
            leg: None,
        },
        PermissionOutcome::Reject { reason, .. } => PermissionMoment {
            tool: call.name.clone(),
            mandate,
            allowed: false,
            detail: reason.clone(),
            remaining: None,
            leg: Some(RefusalLeg::classify(reason)),
        },
    }
}

/// Project a live [`Mandate`] into the dock's budget rows (every touched mandate
/// + every pinned per-tool grant), so the budget bars deplete as the agent spends.
fn budget_rows(mandate: &Mandate) -> Vec<MandateBudget> {
    mandate
        .rows
        .iter()
        .filter(|r| {
            // Show pinned per-tool grants always; kind floors only once touched.
            matches!(r.key, crate::grant_registry::MandateKey::Tool(_))
                || r.calls_made > 0
                || !r.refusals.is_empty()
        })
        .map(|r| MandateBudget {
            label: r.key.label(),
            rate_limit: r.rate_limit,
            spent: r.calls_made,
            per_tool: matches!(r.key, crate::grant_registry::MandateKey::Tool(_)),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HermesGateway;
    use crate::acp::ToolCallRequest;
    use crate::grant_registry::GrantRegistry;
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
        let call =
            ToolCallRequest::new("s1", "tc-1", "web_search", serde_json::json!({"query":"x"}));
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
