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
//! ## The brain — a real closed loop, not a fixed script
//!
//! 9. [`brain`] — the agent BRAIN that the scripted stand-in is replaced by. An
//!    [`brain::LlmBrain`] decides the next step from the running
//!    [`brain::AgentConvo`], OBSERVES each gate verdict, and decides again — a
//!    closed `decide → gate → observe` loop. Two ship: [`brain::LocalBrain`] (a
//!    deterministic, reactive ON-BOX brain — reads the prompt, adapts to refusals)
//!    and [`brain::HttpLlm`] (the live BYO-key LLM path over [`brain::LlmHttpCaller`]).
//!    The operator's [`brain::LlmKeys`] reach the provider and NOWHERE the agent's
//!    reach travels (redacted Debug; never in a tool-call / receipt / wire).
//! 10. [`agent_peer`] — [`agent_peer::HermesAgentPeer`]: the [`acp_client::AcpPeer`]
//!    that runs the brain loop over the SAME `acp_adapter` wire shapes the mock
//!    replays, so the UNCHANGED [`AcpClient`] drives a real confined agent.
//!
//! ## What is REAL vs. the remaining seam (honest)
//!
//! REAL: the [`ToolGateway`](dregg_sdk::ToolGateway) path — `admit` + `invoke`
//! run on the verified executor and yield a genuine [`dregg_turn::TurnReceipt`];
//! the ACP TRANSPORT — real ndjson JSON-RPC framing + a live-capable subprocess
//! spawner; the riding effects; the per-tool grants; the inspector; AND the agent
//! BRAIN itself — a real closed reactive loop ([`brain::LocalBrain`]) or a real
//! BYO-key LLM ([`brain::HttpLlm`], proven over a mock provider, live against a
//! real endpoint). The brain decides + adapts; it is no longer a pre-written list.
//! THE REMAINING SEAM: a live model-provider credential (the BYO key), and
//! compiling the brain's provider client into the exec-denied [`confined`] jail
//! body (it runs `execve`-free, so [`brain::LocalBrain`] already fits) in place of
//! [`confined::stand_in_acp_peer`]. The Nous-Research `hermes-acp` venv subprocess
//! ([`AcpTransport::spawn_hermes`]) is the other live brain path (env-broken here).

pub mod acp;
pub mod acp_client;
pub mod agent_peer;
pub mod attest;
pub mod brain;
pub mod bridge;
#[cfg(feature = "js-agent")]
pub mod card_authoring;
#[cfg(feature = "cockpit-surface")]
pub mod cockpit_surface;
#[cfg(unix)]
pub mod confined;
pub mod confined_body;
#[cfg(unix)]
pub mod egress;
pub mod grant_registry;
#[cfg(unix)]
pub mod host;
#[cfg(feature = "js-agent")]
pub mod live_js;
pub mod mandate;
pub mod mcp_server;
pub mod mock_peer;
#[cfg(all(unix, feature = "node-brain"))]
pub mod node_hands;
// The REAL zkTLS oracle-fact verifier homed here (the crypto seam `dregg-cell`'s
// fail-closed `OracleWitnessedPredicateVerifier` installs). Behind `zk-live`, which
// pulls the heavy `tlsn` MPC-TLS backend `verify_zkoracle_live_host` links.
#[cfg(feature = "zk-live")]
pub mod oracle_fact;
pub mod resident;
#[cfg(feature = "js-agent")]
pub mod run_js;
#[cfg(feature = "screenshot")]
pub mod screenshot;
pub mod surface;
// The REAL TEE attestation-fact verifier homed here (the vendor-crypto seam
// `dregg-cell`'s fail-closed `TeeWitnessedPredicateVerifier` installs): dispatches
// to `dregg-tee-verify`'s NitroVerifier / SnpVerifier and registers under
// `tee_predicate_vk()`. Default build — the deps are light (X.509/P-384/CBOR),
// unlike the `zk-live`-gated oracle seam.
pub mod tee_fact;
pub mod tool_effects;
pub mod world_bridge;

pub use acp::{PermissionOutcome, ToolCallRequest, ToolKind};
pub use acp_client::{
    AcpClient, AcpError, AcpPeer, AcpTransport, JsRunRecord, PromptRun, RunJsHook, StreamEvent,
};
pub use agent_peer::HermesAgentPeer;
pub use attest::{AttestationCarrier, attestation_commitment, messages_body};
#[cfg(feature = "zk-live")]
pub use oracle_fact::{OracleFactProof, ZkOracleFactVerifier};
// THE CROWN — re-export the zkOracle attestation surface a HOST verifies with, so a
// caller attaches + checks a confined turn's attestation without depending on
// `dregg-zkoracle-prove` directly.
pub use brain::{
    AgentConvo, BrainStep, HttpLlm, LlmBrain, LlmHttpCaller, LlmKeys, LocalBrain, MoonshotCaller,
    OpenAICompatCaller, ToolObservation,
};
pub use bridge::{HermesGateway, ToolMarket};
// THE WELD — Hermes as a grain-jail CONFINED BODY: its ACP tool-call stream rides
// a `grain_jail::BodyChannel`, every proposal still a cap-gated receipted turn
// through the proven `ToolGateway`.
pub use confined_body::{
    AcpBodyChannel, ConfinedHermesReport, acp_call_of_proposal, confined_hermes_channel,
    drive_confined_hermes, proposal_of_acp_call,
};
#[cfg(unix)]
pub use confined_body::{drive_confined_hermes_in_jail, model_egress_policy};
pub use dregg_zkoracle_prove::{
    AnthropicConfig, ProveError, VerifiedZkOracle, ZkOracleAttestation, ZkOracleError,
    verify_zkoracle,
};
#[cfg(unix)]
pub use egress::{EgressGrant, EgressNetGrant, EgressPolicy, provider_host_port};
pub use grant_registry::{GrantRegistry, MandateKey};
#[cfg(unix)]
pub use host::{DreggHost, HostedAgentReport, HostedToolVerdict};
pub use mcp_server::{ConfinedToolResult, DREGG_TOOL_NAMES, McpServer, McpToolHost};
#[cfg(unix)]
pub use world_bridge::{BridgeWorld, SocketWorldSink, serve_world_bridge};

// Re-export the grounding SDK types a HOST needs to construct a confined gateway
// (mint a root token, build a runtime) WITHOUT depending on `dregg-sdk` directly —
// e.g. deos-zed-full's agent-panel mount builds its own tightly-confined
// `HermesGateway` over these. The enforcement still lives entirely in `dregg-sdk`;
// this is a convenience re-export of the constructor surface.
#[cfg(feature = "js-agent")]
pub use card_authoring::{AuthorCardOutcome, CardAuthoringTool};
pub use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken, ToolGrant};
#[cfg(feature = "js-agent")]
pub use live_js::{LiveAuthoringHands, LiveComposeHands, LiveJsHands, script_of_call};
pub use mandate::{Mandate, MandateRow};
pub use mock_peer::{MockHermesPeer, ScriptedCall};
#[cfg(all(unix, feature = "node-brain"))]
pub use node_hands::{NodeHandsError, NodeJsHands, agent_cell_of, check_endpoint};
pub use resident::{AnthropicCaller, ResidentBrain, resident_brain_from_env};
#[cfg(feature = "js-agent")]
pub use run_js::{
    RunJsAuthorOutcome, RunJsAuthoringTool, RunJsComposeOutcome, RunJsComposeTool, RunJsError,
    RunJsOutcome, RunJsTool,
};
