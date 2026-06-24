//! # deos-hermes — Hermes as a CONFINED deos agent.
//!
//! Hermes (Nous Research's self-improving agent, `~/pug/hermes-agent`) exposes
//! itself over the **Agent Client Protocol** (ACP): a deos-side ACP client
//! connects, and EVERY Hermes tool-call is intercepted before it runs. Instead
//! of trusting Hermes (or an editor's allow/deny prompt), deos routes the
//! tool-call through the PROVEN [`ToolGateway`](dregg_sdk::ToolGateway): it
//! becomes a cap-gated, metered, RECEIPTED dregg turn on the verified executor —
//! or an in-band refusal Hermes sees. This is the ADOS thesis (a turn = the
//! exercise of an attenuable proof-carrying token over owned state, leaving a
//! verifiable receipt) realized with a REAL agent.
//!
//! ## The seam (this crate's first slice)
//!
//! 1. [`acp`] — the ACP wire subset deos intercepts: a [`acp::ToolCallRequest`]
//!    (built from an ACP `tool_call` start / `session/request_permission`) and
//!    the [`acp::PermissionOutcome`] deos returns.
//! 2. [`grant_registry`] — deos's confinement: a [`dregg_sdk::ToolGrant`] per
//!    Hermes [`acp::ToolKind`] (scope + rate ceiling + deadline).
//! 3. [`bridge`] — [`bridge::HermesGateway`]: lazily admits a cap-gated worker
//!    per kind and routes each tool-call through
//!    [`ToolGateway::invoke`](dregg_sdk::ToolGateway::invoke), mapping the
//!    verdict back to an ACP outcome.
//!
//! The enforcement is entirely the proven `ToolGateway`'s (`delegAdmit` mirror +
//! executor-side `mandate_program` backstop); this crate is the ACP↔gate seam,
//! nothing more.
//!
//! ## Beyond the seam — the live loop, riding effects, per-tool grants
//!
//! 4. [`acp_client`] — the REAL ndjson JSON-RPC ACP CLIENT. It drives
//!    `initialize` → `session/new` → `session/prompt`, consumes streamed
//!    `session/update`s, and answers each `session/request_permission` by
//!    running [`HermesGateway::admit_call`] and replying with the mapped ACP
//!    outcome. It is transport-agnostic ([`acp_client::AcpPeer`]): it can spawn a
//!    live `hermes-acp` subprocess ([`acp_client::AcpTransport`]) OR run against
//!    the [`mock_peer::MockHermesPeer`] that replays the real `acp_adapter`
//!    message shapes. The end-to-end loop runs over the mock (the live install
//!    in this env is broken — its venv lacks the `acp` module); the SAME driver
//!    runs over the subprocess once that is fixed.
//! 5. [`tool_effects`] — a tool-call's actual payload becomes a `Vec<Effect>`
//!    witness that rides the SAME metered turn as the counter advance, so the
//!    receipt witnesses WHAT the call did (the path, the URL), not just the meter.
//! 6. [`grant_registry`] now supports per-TOOL grants over the per-kind floor
//!    (tightest-wins), each its own cap-gated, independently-metered worker.
//! 7. [`mandate`] — the mandate inspector: an agent's live confinement (grants,
//!    budgets spent, receipts, refusals) made legible — ADOS made visible.
//! 8. [`surface`] — a documented, ready-to-mount `CockpitSurface` sketch for the
//!    confined-Hermes agent dock (does NOT depend on starbridge-v2).
//!
//! ## What is REAL vs. MOCK (honest)
//!
//! REAL: the [`ToolGateway`](dregg_sdk::ToolGateway) path — `admit` + `invoke`
//! run on the verified executor and yield a genuine [`dregg_turn::TurnReceipt`];
//! the ACP TRANSPORT — real ndjson JSON-RPC framing + a live-capable subprocess
//! spawner; the riding effects; the per-tool grants; the inspector.
//! MOCK: the Hermes PEER in the tested end-to-end loop — a faithful replay of
//! `acp_adapter`'s message shapes, because the live `hermes-acp` install in this
//! environment is broken and a working one needs model credentials. The seam is
//! exercised identically over either peer.

pub mod acp;
pub mod acp_client;
pub mod bridge;
#[cfg(feature = "cockpit-surface")]
pub mod cockpit_surface;
#[cfg(unix)]
pub mod confined;
#[cfg(unix)]
pub mod egress;
#[cfg(unix)]
pub mod host;
pub mod grant_registry;
pub mod mandate;
pub mod mcp_server;
#[cfg(feature = "js-agent")]
pub mod run_js;
#[cfg(feature = "js-agent")]
pub mod card_authoring;
#[cfg(feature = "js-agent")]
pub mod live_js;
pub mod mock_peer;
#[cfg(feature = "screenshot")]
pub mod screenshot;
pub mod surface;
pub mod tool_effects;

pub use acp::{PermissionOutcome, ToolCallRequest, ToolKind};
pub use acp_client::{
    AcpClient, AcpError, AcpPeer, AcpTransport, JsRunRecord, PromptRun, RunJsHook, StreamEvent,
};
pub use bridge::HermesGateway;
#[cfg(unix)]
pub use egress::{EgressGrant, EgressPolicy};
#[cfg(unix)]
pub use host::{DreggHost, HostedAgentReport};
pub use grant_registry::{GrantRegistry, MandateKey};
pub use mcp_server::{ConfinedToolResult, McpServer, McpToolHost, DREGG_TOOL_NAMES};

// Re-export the grounding SDK types a HOST needs to construct a confined gateway
// (mint a root token, build a runtime) WITHOUT depending on `dregg-sdk` directly —
// e.g. deos-zed-full's agent-panel mount builds its own tightly-confined
// `HermesGateway` over these. The enforcement still lives entirely in `dregg-sdk`;
// this is a convenience re-export of the constructor surface.
pub use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken, ToolGrant};
pub use mandate::{Mandate, MandateRow};
pub use mock_peer::{MockHermesPeer, ScriptedCall};
#[cfg(feature = "js-agent")]
pub use run_js::{RunJsAuthorOutcome, RunJsAuthoringTool, RunJsError, RunJsOutcome, RunJsTool};
#[cfg(feature = "js-agent")]
pub use card_authoring::{AuthorCardOutcome, CardAuthoringTool};
#[cfg(feature = "js-agent")]
pub use live_js::{script_of_call, LiveAuthoringHands, LiveJsHands};
