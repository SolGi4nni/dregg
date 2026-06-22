//! The ACP wire subset deos-hermes intercepts.
//!
//! Hermes exposes itself over the **Agent Client Protocol** (ACP): a JSON-RPC
//! stdio protocol of `session/new`, `session/prompt`, streaming `session/update`
//! notifications, and — the one that matters for confinement —
//! `session/request_permission`. We do NOT re-model all of ACP here (the full
//! schema lives in the `agent-client-protocol` crate / Hermes's
//! `acp_adapter`); we model exactly the two messages the gate sits on:
//!
//! * [`ToolCallRequest`] — the inbound description of a tool-call Hermes wants
//!   to run. It is built from EITHER an ACP `session/update` `tool_call` start
//!   (`acp_adapter/tools.py::build_tool_start` → `ToolCallStart`) OR the
//!   `tool_call` payload carried on a `session/request_permission`
//!   (`acp_adapter/permissions.py::_build_permission_tool_call` →
//!   `update_tool_call`). Both carry the fields we need: a `tool_call_id`, the
//!   tool `name`/`kind`, and the `raw_input` arguments.
//! * [`PermissionOutcome`] — what the deos-side ACP CLIENT returns to Hermes
//!   for that `request_permission`: ALLOW (with a receipt the editor can show)
//!   or REJECT (with the in-band refusal reason). This is the polarity the
//!   gate decides.
//!
//! THE SEAM IN ONE SENTENCE: Hermes asks "may I run this tool-call?" over ACP;
//! deos answers by running it through [`crate::HermesGateway`] — a cap-gated,
//! metered, receipted dregg turn — and returns ALLOW+receipt or REJECT+reason.

use serde::{Deserialize, Serialize};

/// The ACP `ToolKind` taxonomy, mirrored from Hermes's
/// `acp_adapter/tools.py::TOOL_KIND_MAP` / `get_tool_kind`. Every Hermes tool
/// classifies into exactly one kind; the deos grant registry
/// ([`crate::GrantRegistry`]) keys the DEFAULT scope/rate off this kind, so an
/// unknown tool still lands under a known confinement class (`Other`,
/// the most-restricted default).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ToolKind {
    /// Reads state (read_file, search content, snapshot, …). Side-effect-free.
    Read,
    /// Mutates the workspace (write_file, patch, skill_manage). The dangerous class.
    Edit,
    /// Runs a command / drives a process (terminal, execute_code, browser_click).
    Execute,
    /// Reads the world over the network (web_search, web_extract, browser_navigate).
    Fetch,
    /// Searches (search_files).
    Search,
    /// Everything else (todo, meta) — the most-restricted default.
    Other,
}

impl ToolKind {
    /// Map a Hermes tool NAME to its ACP kind, byte-faithful to
    /// `acp_adapter/tools.py::TOOL_KIND_MAP`. Unknown names default to `Other`
    /// (the Python `get_tool_kind` default).
    pub fn of_tool(name: &str) -> ToolKind {
        match name {
            "read_file" | "skill_view" | "skills_list" | "browser_snapshot" | "browser_vision"
            | "browser_get_images" | "vision_analyze" => ToolKind::Read,
            "write_file" | "patch" | "skill_manage" => ToolKind::Edit,
            "terminal" | "process" | "execute_code" | "browser_click" | "browser_type"
            | "browser_scroll" | "browser_press" | "browser_back" | "delegate_task"
            | "image_generate" | "text_to_speech" => ToolKind::Execute,
            "web_search" | "web_extract" | "browser_navigate" => ToolKind::Fetch,
            "search_files" => ToolKind::Search,
            _ => ToolKind::Other,
        }
    }
}

/// An inbound Hermes tool-call, as deos sees it over ACP.
///
/// Constructed from an ACP `tool_call` start update OR the `tool_call` payload
/// on a `session/request_permission`. The `name` + `kind` + `arguments` are the
/// gate's inputs; `tool_call_id` and `session_id` are the ACP correlation keys
/// (echoed back on the [`PermissionOutcome`]).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ToolCallRequest {
    /// The ACP session this call belongs to.
    pub session_id: String,
    /// The ACP tool-call id (correlates the outcome back to the request).
    pub tool_call_id: String,
    /// The Hermes tool name (e.g. `"web_search"`, `"terminal"`, `"write_file"`).
    pub name: String,
    /// The ACP tool kind (derived from `name` via [`ToolKind::of_tool`] if the
    /// wire omits it).
    pub kind: ToolKind,
    /// The tool arguments (ACP `raw_input`).
    pub arguments: serde_json::Value,
}

impl ToolCallRequest {
    /// Build a request from the raw ACP fields, deriving the `kind` from the
    /// tool name (the Hermes default classification).
    pub fn new(
        session_id: impl Into<String>,
        tool_call_id: impl Into<String>,
        name: impl Into<String>,
        arguments: serde_json::Value,
    ) -> ToolCallRequest {
        let name = name.into();
        let kind = ToolKind::of_tool(&name);
        ToolCallRequest {
            session_id: session_id.into(),
            tool_call_id: tool_call_id.into(),
            name,
            kind,
            arguments,
        }
    }
}

/// What deos returns to Hermes over ACP for a `session/request_permission`.
///
/// On the ACP wire this becomes an `AllowedOutcome { option_id: "allow_once" }`
/// (mapped to Hermes's `"once"`, see `acp_adapter/permissions.py`) when
/// [`PermissionOutcome::Allow`], or a rejection (`deny`) when
/// [`PermissionOutcome::Reject`]. The deos extension over plain ACP: an ALLOW
/// carries the dregg **receipt id** + remaining budget, and a REJECT carries
/// the IN-BAND refusal `reason` — so the editor surface (and Hermes's own
/// trajectory) sees exactly which mandate leg bit.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "outcome", rename_all = "snake_case")]
pub enum PermissionOutcome {
    /// The cap-gated metered turn COMMITTED. The call may proceed; the editor
    /// can show the receipt. Maps to ACP `allow_once`.
    Allow {
        /// The ACP tool-call this answers.
        tool_call_id: String,
        /// The dregg turn receipt id (proof the metered turn committed).
        receipt: String,
        /// Calls remaining on this tool's mandate after this one.
        remaining: i64,
    },
    /// The gate REFUSED the call in-band (no turn, no spend). Maps to ACP
    /// `deny`. The `reason` names the leg that bit (scope/deadline/rate/error).
    Reject {
        /// The ACP tool-call this answers.
        tool_call_id: String,
        /// The human-readable refusal reason (the `GatewayRefusal` / error text).
        reason: String,
    },
}

impl PermissionOutcome {
    /// The ACP option id this outcome maps to (`allow_once` / `deny`), matching
    /// `acp_adapter/permissions.py::_OPTION_ID_TO_HERMES`.
    pub fn acp_option_id(&self) -> &'static str {
        match self {
            PermissionOutcome::Allow { .. } => "allow_once",
            PermissionOutcome::Reject { .. } => "deny",
        }
    }

    /// Whether the call was admitted.
    pub fn allowed(&self) -> bool {
        matches!(self, PermissionOutcome::Allow { .. })
    }
}
