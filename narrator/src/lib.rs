//! # dregg-narrator — a HOSTED narrator behind a HARD, self-enforced USD spend ceiling.
//!
//! The fiction engine wants a good hosted model to narrate, but a hosted model spends real
//! money per call. AWS Budgets are notification-only and lag hours — useless as a ceiling. So
//! this crate enforces the ceiling itself, at OUR invocation layer:
//!
//! * [`BudgetLedger`] — a persisted, concurrency-safe, fail-closed USD ledger. Every hosted call
//!   is a **pre-flight reservation** (refused BEFORE the network if it would exceed the cap) →
//!   the network call → a **post-flight true-up** with the response's real token usage, persisted
//!   atomically under an advisory file lock. A corrupt ledger refuses everything; a missing one
//!   starts at $0.00.
//! * [`ModelRegistry`] — the pinned price book. **The ledger refuses any model it has no price
//!   for** ([`NarratorError::UnpricedModel`]): you cannot cap a cost you do not know. Unverified
//!   rates are pinned as deliberate UPPER BOUNDS (see [`ledger::PriceSource`]).
//! * [`Narrator`] — a hosted-model tier (AWS Bedrock Nova/Claude, OR any OpenAI-compatible endpoint
//!   via [`OpenAiCompatClient`] — Chutes / Bittensor, vLLM, OpenRouter, a local proxy), then local
//!   Ollama, then deterministic Scripted, with honest fallback. [`Narrator::auto`] resolves the
//!   hosted provider from `DREGG_NARRATOR`, and every result reports the [`Narration::kind`] that
//!   ACTUALLY produced the text — never a model that did not narrate.

mod backend;
mod bedrock;
pub mod ledger;
pub mod models;
mod narrator;
pub mod ollama;
pub mod openai;

pub use backend::{
    metered_converse, AttestationSummary, ConverseBackend, ConverseMessage, ConverseRequest,
    ConverseResponse, Role, ToolCall, ToolDef,
};
pub use bedrock::BedrockClient;
pub use ledger::{BudgetLedger, LedgerState, ModelSpend, PriceSource, Pricing, Reservation};
pub use models::{ModelRegistry, CLAUDE_HAIKU_4_5, DEFAULT_MODEL, NOVA_2_LITE, NOVA_PRO};
pub use narrator::{hosted_provider, HostedProvider, Narration, Narrator};
pub use ollama::OllamaBackend;
pub use openai::{build_chat_body, parse_chat_response, OpenAiCompatClient};

/// Everything that can go wrong at the narrator layer.
#[derive(Debug, thiserror::Error)]
pub enum NarratorError {
    /// The pre-flight reservation would push the total past the cap — refused BEFORE the network.
    #[error("budget exhausted: ${spent:.6} already spent of a ${cap:.2} cap; this call's reservation would exceed it (refused before any network call)")]
    BudgetExhausted { spent: f64, cap: f64 },

    /// The model has no pinned price — refused fail-closed (a budget cannot cap an unknown cost).
    #[error("unpriced model `{model}`: no pinned price in the registry — refusing (a budget cannot be enforced on a cost we do not know). Pin its rate before use.")]
    UnpricedModel { model: String },

    /// The ledger file exists but does not parse — refuse ALL calls until an operator resets it.
    #[error("ledger corrupt at {path}: {reason} — refusing all calls (fail-closed); reset it explicitly to continue")]
    LedgerCorrupt { path: String, reason: String },

    /// No configured backend produced text.
    #[error("no narrator backend produced text: {0}")]
    AllBackendsFailed(String),

    /// A backend (Bedrock/Ollama) returned an error.
    #[error("backend error: {0}")]
    Backend(String),

    /// A ledger I/O error.
    #[error("ledger io error: {0}")]
    Io(String),
}
