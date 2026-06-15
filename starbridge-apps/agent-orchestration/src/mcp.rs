//! # Live MCP tool-call binding — an agent loop's tool invocation IS a verified worker step.
//!
//! The seam the record names: *each integrator serializes "an agent did X" at ONE place (buildr's
//! `PostToolUse`, builders' `recordPhaseComplete`, sig's `swarm-callback`, simbi's `AgentRun`) — today a
//! mutable log line; with dregg a signed, cap-checked, budget-metered, proof-carrying turn.* For an
//! LLM agent the tool call IS that seam: the MCP `tools/call` JSON-RPC request the model emits. This
//! module binds it — an MCP tool call by a worker is run AS a verified [`crate::WorkStep`] through the
//! real executor, so the on-ledger receipt cryptographically binds the EXACT tool name + arguments the
//! loop invoked, and a call to a tool OUTSIDE the worker's mandate is REFUSED in the fire path.
//!
//! ## What this closes
//!
//! Before: the orchestration's [`crate::Tool`] was an enum the engine gated, but nothing tied a worker's
//! REAL tool invocation (the MCP request) to the gated step — the binding was by convention. Now an MCP
//! `tools/call` is mapped to a `(Tool, cost)`, run through [`crate::OrchestrationEngine::step`], and the
//! call's content-address (`blake3(name ‖ arguments)`) is bound into the step's sub-task — so the
//! receipt PROVES which tool, with which arguments, the worker ran, and the mandate gate (scope ∧
//! budget) decided it. A worker that emits an MCP call for a tool its mandate does not grant is refused
//! ([`crate::OrchestrationError::OutOfMandate`]) BEFORE the call has any effect — the enforcement the
//! four integrators all punted on, at the exact seam.
//!
//! ## The mapping (an integration point, made explicit)
//!
//! [`tool_for_mcp_name`] maps an MCP tool name to the orchestration capability it exercises +
//! a default cost. A deployment customizes this for its toolset; the DEFAULT covers the common
//! agent-loop tools (`fetch`/`read_file` → [`Tool::Read`], `search`/`grep` → [`Tool::Search`],
//! `summarize` → [`Tool::Summarize`], `write_file`/`edit` → [`Tool::Write`], `transfer`/`pay` →
//! [`Tool::Spend`]). An UNKNOWN tool maps to `None` and is refused (fail-closed: a tool the policy does
//! not classify cannot be run).

use crate::{
    OrchestrationEngine, OrchestrationError, OrchestrationLog, Tool, WorkStep, WorkerSlot,
};

/// One MCP `tools/call` request — the JSON-RPC params an LLM agent emits to invoke a tool. The
/// content-address of `(name, arguments)` is what the verified step binds, so the receipt proves the
/// exact call. (The transport/JSON-RPC framing is the host's; this is the decoded call.)
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct McpToolCall {
    /// The MCP tool name the model invoked (e.g. `"search"`, `"write_file"`).
    pub name: String,
    /// The tool arguments, as the model passed them (the MCP `arguments` object). Bound into the
    /// step's content-address so the receipt pins WHICH arguments ran.
    pub arguments: serde_json::Value,
}

impl McpToolCall {
    /// A tool call.
    pub fn new(name: impl Into<String>, arguments: serde_json::Value) -> Self {
        Self {
            name: name.into(),
            arguments,
        }
    }

    /// The **content-address** of this call — `blake3(name ‖ canonical-json(arguments))`, the digest the
    /// verified step binds so the receipt proves the exact tool + arguments the worker ran. Deterministic
    /// (a third party recomputes it from the published call).
    pub fn digest(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-mcp-tool-call\x01");
        h.update(self.name.as_bytes());
        h.update(b"\x00");
        // serde_json::to_vec on a Value is canonical enough for binding (object key order is the
        // serializer's; for a stronger binding a host canonicalizes upstream — named, not faked).
        let args = serde_json::to_vec(&self.arguments).unwrap_or_default();
        h.update(&args);
        *h.finalize().as_bytes()
    }

    /// A short hex of the content-address (for logs / the step sub-task label).
    pub fn digest_hex(&self) -> String {
        self.digest()[..8].iter().map(|b| format!("{b:02x}")).collect()
    }
}

/// The orchestration capability an MCP tool exercises + its default metered cost. The Rust image of "a
/// tool call is the exercise of an attenuable capability over owned state."
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ToolBinding {
    /// The orchestration [`Tool`] (the scope axis the worker's mandate gates).
    pub tool: Tool,
    /// The default computron cost metered against the worker's sub-budget + the swarm budget.
    pub cost: u64,
}

/// **The MCP-name → capability map** — classify an MCP tool name into the orchestration capability it
/// exercises (the scope) + a default cost (the budget). An UNKNOWN tool maps to `None` and is REFUSED
/// (fail-closed: an unclassified tool cannot be run under a mandate). A deployment overrides this for
/// its own toolset; the default covers the common agent-loop tools.
pub fn tool_for_mcp_name(mcp_name: &str) -> Option<ToolBinding> {
    let b = |tool, cost| Some(ToolBinding { tool, cost });
    match mcp_name {
        // Read tools (fetch a document / a URL / a file) — the least-privilege baseline.
        "fetch" | "read_file" | "read" | "get" | "http_get" => b(Tool::Read, 50),
        // Search tools (query an index / corpus / the filesystem).
        "search" | "grep" | "web_search" | "find" | "query" => b(Tool::Search, 100),
        // Summarize / transform.
        "summarize" | "transform" | "extract" | "synthesize" => b(Tool::Summarize, 150),
        // Write tools (mutate the shared workspace) — privileged.
        "write_file" | "edit" | "apply_patch" | "write" | "put" => b(Tool::Write, 200),
        // Spend tools (pay an external API / move treasury) — most privileged.
        "transfer" | "pay" | "purchase" | "spend" | "charge" => b(Tool::Spend, 300),
        _ => None,
    }
}

/// Why running an MCP tool call as a verified step failed.
#[derive(Clone, Debug)]
pub enum McpStepError {
    /// The MCP tool name is not classified by [`tool_for_mcp_name`] — fail-closed (an unknown tool
    /// cannot be run under a mandate). Carries the offending name.
    UnknownTool(String),
    /// The verified step was refused — out-of-mandate (the tool's capability is outside the worker's
    /// scope, or the cost breaches its sub-budget) or executor-refused (the `AffineLe` swarm-budget
    /// gate). The real, in-the-fire-path refusal.
    Refused(OrchestrationError),
}

impl std::fmt::Display for McpStepError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            McpStepError::UnknownTool(n) => write!(
                f,
                "MCP tool `{n}` is not classified by the orchestration policy (fail-closed: refused)"
            ),
            McpStepError::Refused(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for McpStepError {}

/// **Run an MCP tool call AS a verified worker step.** This is the live-MCP binding: the `call` a
/// worker loop emits is classified ([`tool_for_mcp_name`]), then run through the verified executor as a
/// [`crate::WorkStep`] whose sub-task is the call's content-address (`mcp/<name>/<digest>`), so the
/// committed receipt cryptographically binds WHICH tool, with WHICH arguments, the worker ran. The
/// mandate gate decides it in the fire path:
///   * an UNKNOWN tool ⇒ [`McpStepError::UnknownTool`] (fail-closed, nothing submitted);
///   * a tool outside the worker's granted scope, or over its sub-budget ⇒
///     [`McpStepError::Refused`] ([`crate::OrchestrationError::OutOfMandate`], in the fire path);
///   * an over-swarm-budget call ⇒ [`McpStepError::Refused`] (the executor's `AffineLe` gate).
///
/// On commit the receipt is appended to `log` (the durable, auditable chain) — so an auditor later
/// proves the worker invoked ONLY tools its mandate granted, at the arguments the chain records.
pub fn step_from_mcp_call(
    engine: &mut OrchestrationEngine,
    worker: WorkerSlot,
    call: &McpToolCall,
    log: &mut OrchestrationLog,
) -> Result<dregg_turn::TurnReceipt, McpStepError> {
    let binding = tool_for_mcp_name(&call.name)
        .ok_or_else(|| McpStepError::UnknownTool(call.name.clone()))?;
    // The step's sub-task is the call's content-address — so the receipt binds the exact MCP call.
    let sub_task = format!("mcp/{}/{}", call.name, call.digest_hex());
    let step = WorkStep::new(worker, binding.tool, binding.cost, &sub_task);
    engine.step(&step, log).map_err(McpStepError::Refused)
}

/// Classify an MCP call to the [`Tool`] it exercises WITHOUT running it — the off-ledger pre-flight a
/// host uses to decide "may this worker even attempt this tool" before building a turn (the same
/// classification [`step_from_mcp_call`] uses). Returns the [`ToolBinding`] or `None` (unknown).
pub fn classify(call: &McpToolCall) -> Option<ToolBinding> {
    tool_for_mcp_name(&call.name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_mcp_tools_map_to_capabilities() {
        assert_eq!(tool_for_mcp_name("search").unwrap().tool, Tool::Search);
        assert_eq!(tool_for_mcp_name("read_file").unwrap().tool, Tool::Read);
        assert_eq!(tool_for_mcp_name("write_file").unwrap().tool, Tool::Write);
        assert_eq!(tool_for_mcp_name("pay").unwrap().tool, Tool::Spend);
        // an unknown tool is unclassified (fail-closed).
        assert!(tool_for_mcp_name("rm_minus_rf_the_universe").is_none());
    }

    #[test]
    fn the_digest_binds_name_and_arguments() {
        let a = McpToolCall::new("search", serde_json::json!({"q": "dregg"}));
        let b = McpToolCall::new("search", serde_json::json!({"q": "dregg"}));
        let c = McpToolCall::new("search", serde_json::json!({"q": "other"}));
        let d = McpToolCall::new("grep", serde_json::json!({"q": "dregg"}));
        assert_eq!(a.digest(), b.digest(), "same call ⇒ same digest");
        assert_ne!(a.digest(), c.digest(), "different args ⇒ different digest");
        assert_ne!(a.digest(), d.digest(), "different tool ⇒ different digest");
    }

    #[test]
    fn an_unknown_tool_classifies_to_none() {
        let call = McpToolCall::new("exfiltrate_secrets", serde_json::json!({}));
        assert!(classify(&call).is_none());
    }
}
