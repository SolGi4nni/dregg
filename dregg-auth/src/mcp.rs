//! The MCP gateway profile — a thin, standalone middleware shape.
//!
//! An MCP server (or any tool-dispatch host) sits in front of an agent and, for
//! every incoming tool call, must decide: *is this call inside the agent's
//! grant?* The world's current answer is "ship an unscoped API key in an env
//! var and hope." dregg-auth's answer is: the agent carries a scoped token, the
//! gateway holds only the issuer's public key, and the decision is made
//! **offline** — then logged as a receipt (the L2 audit seed).
//!
//! This module is deliberately STANDALONE: it depends on nothing but this crate.
//! It defines a [`ToolGate`] trait (the seam the node's `mcp.rs` per-tool cap
//! gate can later implement) and a concrete [`OfflineGate`] that needs only a
//! public key. No node, no turn, no circuit.

use crate::{Decision, Request, verify_offline};

/// A tool-call gate: given an agent's token and a requested tool call, decide.
///
/// The node's MCP layer can implement this trait to slot dregg-auth into an
/// existing dispatch path; the [`OfflineGate`] below is the batteries-included
/// implementation for the standalone case.
pub trait ToolGate {
    /// Decide whether `call` (carried by `token`) is permitted, and produce a
    /// receipt line either way (allow and deny are both auditable events).
    fn admit(&self, token_encoded: &str, call: &ToolCall) -> Gated;
}

/// An incoming MCP tool call: the tool name + its arguments + a clock.
#[derive(Clone, Debug)]
pub struct ToolCall {
    /// The MCP tool being invoked.
    pub tool: String,
    /// The arguments, as `(name, value)` pairs (carried into the receipt).
    pub args: Vec<(String, String)>,
    /// The gateway's clock (unix seconds); `None` = wall-clock.
    pub now: Option<i64>,
}

impl ToolCall {
    /// A bare tool call (no args).
    pub fn new(tool: &str) -> Self {
        Self {
            tool: tool.to_string(),
            args: Vec::new(),
            now: None,
        }
    }

    /// Attach `(name, value)` arguments.
    pub fn arg(mut self, name: &str, value: &str) -> Self {
        self.args.push((name.to_string(), value.to_string()));
        self
    }

    /// Pin the gateway clock for a deterministic decision.
    pub fn at(mut self, now: i64) -> Self {
        self.now = Some(now);
        self
    }

    fn to_request(&self) -> Request {
        let mut req = Request::tool(&self.tool);
        req.now = self.now;
        req.args = self
            .args
            .iter()
            .map(|(k, v)| format!("{k}={v}"))
            .collect();
        req
    }
}

/// The outcome of a gated tool call: the decision + the audit receipt.
#[derive(Clone, Debug)]
pub struct Gated {
    /// The allow/deny decision (with a human reason).
    pub decision: Decision,
    /// The audit receipt line for this call (emit it to a log — the L2 seed).
    pub receipt: Receipt,
}

impl Gated {
    /// Was the call admitted?
    pub fn admitted(&self) -> bool {
        self.decision.allowed()
    }
}

/// One audit receipt: who asked for what, when, and what was decided.
///
/// This is the L2 seed — a chain of these is an agent's behavioral ledger. It is
/// intentionally plain and serializable; the gateway emits one line per call.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Receipt {
    /// The subject (agent) the token was confined to, if recoverable.
    pub subject: Option<String>,
    /// The tool that was requested.
    pub tool: String,
    /// The arguments (`name=value`).
    pub args: Vec<String>,
    /// The gateway clock used (unix seconds), if pinned.
    pub at: Option<i64>,
    /// Whether the call was admitted.
    pub allowed: bool,
    /// The human-readable reason (allow, or which constraint failed).
    pub reason: String,
}

impl Receipt {
    /// Render the receipt as a single audit line.
    pub fn line(&self) -> String {
        let verdict = if self.allowed { "ALLOW" } else { "DENY " };
        let subj = self.subject.as_deref().unwrap_or("?");
        let args = if self.args.is_empty() {
            String::new()
        } else {
            format!(" [{}]", self.args.join(", "))
        };
        format!(
            "{verdict} subject={subj} tool={}{args} :: {}",
            self.tool, self.reason
        )
    }

    /// Render the receipt as a JSON line (for structured log ingestion).
    pub fn json(&self) -> String {
        serde_json::to_string(self).unwrap_or_else(|e| format!("{{\"receipt_error\":\"{e}\"}}"))
    }
}

/// The batteries-included, fully-offline gate: holds only the issuer's public
/// key. This is the standalone product profile — drop it in front of an MCP
/// server and it scopes every tool call with no network and no node.
pub struct OfflineGate {
    public_key_hex: String,
}

impl OfflineGate {
    /// Build a gate that verifies agent tokens against `public_key_hex`.
    pub fn new(public_key_hex: impl Into<String>) -> Self {
        Self {
            public_key_hex: public_key_hex.into(),
        }
    }
}

impl ToolGate for OfflineGate {
    fn admit(&self, token_encoded: &str, call: &ToolCall) -> Gated {
        let request = call.to_request();
        let decision = verify_offline(token_encoded, &self.public_key_hex, &request);

        let receipt = Receipt {
            // The subject is recovered from the token's confined `user()` fact
            // during verification — not invented from the request.
            subject: decision.subject().map(|s| s.to_string()),
            tool: call.tool.clone(),
            args: request.args.clone(),
            at: call.now,
            allowed: decision.allowed(),
            reason: decision.reason().to_string(),
        };

        Gated { decision, receipt }
    }
}
