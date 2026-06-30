//! `dregg-agent` — the **open-source dregg agent runtime**.
//!
//! A confined autonomous agent, realized over the dregg substrate alone (no
//! cloud, no hosting, no private control plane). An agent is a *brain* proposing
//! actions, each one:
//!
//! 1. **bounded** — metered against a [`budget::ReplenishingBudget`] cell through
//!    the [`meter::Meter`] trait (the spend bound; an exhausted budget refuses
//!    further actions in-band, so a runaway is contained);
//! 2. **gated** — cap-checked against an attenuable bundle / powerbox minted from
//!    the [`cred`] credential lattice via [`grant`] (`mint_caps` /
//!    `attenuate_caps`); attenuation can only ever *narrow* reach;
//! 3. **receipted** — sealed into a prev-hash-chained, ed25519-signed
//!    [`receipt::ReceiptChain`] so the whole run is a verifiable artifact
//!    ([`agent::verify_agent_run`]) a non-witness can re-check end to end.
//!
//! The **brain** is the [`agent::AgentBrain`] seam. A [`agent::PlannedBrain`]
//! drives the deterministic path; the [`brain::OpenAICompatBrain`] drives a real
//! autonomous agent against **any OpenAI-compatible / Hermes model** (BYO key,
//! recorded transport for tests, the live HTTP transport behind the off-by-default
//! `live-brain` feature). The [`harness`] confines a BYO child-process brain
//! behind the same seam.
//!
//! The agent reaches live capabilities (`run_tests` / `verify_deploy` /
//! `check_health`) through the [`toolkit`] — a registry of cap-gated, metered,
//! receipted tools. The compute tools take an **injected runner** ([`toolkit::RunFn`]),
//! so this crate owns the witness binding but never a sandbox engine: a host (the
//! cloud) wires whatever sandbox it likes behind the seam, and the open core has
//! **zero** compute-engine dependency.
//!
//! [`federation_qa`] is the quorum-QA core: independent operators re-witness an
//! agent's `(command, code_root)` binding and attest agreement.
//!
//! Everything here depends only on the substrate primitives (serde, blake3,
//! ed25519, postcard, base64) — it is AGPL and public on the dregg substrate, and
//! the cloud *wraps* it (depends on it), never the reverse. See
//! `docs/AGENT-RUNTIME-OPEN-SOURCE.md`.

// ── the substrate primitives the runtime is built from ───────────────────────
pub mod cred;
pub mod grant;
pub mod receipt;

// ── the bound ────────────────────────────────────────────────────────────────
pub mod budget;
pub mod meter;

// ── the agent runtime ────────────────────────────────────────────────────────
pub mod agent;
pub mod brain;
pub mod federation_qa;
pub mod harness;
pub mod toolkit;
