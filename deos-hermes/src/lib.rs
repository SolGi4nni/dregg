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
//! ## What is a first-slice STUB vs REAL
//!
//! REAL: the [`ToolGateway`](dregg_sdk::ToolGateway) path — `admit` + `invoke`
//! run on the verified executor and yield a genuine [`dregg_turn::TurnReceipt`].
//! STUB (first slice): the ACP TRANSPORT — connecting to a live `hermes acp`
//! subprocess and parsing real JSON-RPC frames is roadmap (see crate docs /
//! the report). Here a [`acp::ToolCallRequest`] is fed in directly (a mocked
//! ACP source), so the slice proves the load-bearing seam — tool-call → gated
//! receipted turn — grounded in the real gateway.

pub mod acp;
pub mod bridge;
pub mod grant_registry;

pub use acp::{PermissionOutcome, ToolCallRequest, ToolKind};
pub use bridge::HermesGateway;
pub use grant_registry::GrantRegistry;
