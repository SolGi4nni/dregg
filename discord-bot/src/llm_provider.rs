//! BYO multi-provider LLM abstraction — Anthropic / OpenAI / OpenRouter / Kimi
//! (Moonshot) / DeepSeek.
//!
//! A [`Provider`] declares everything needed to call an inference provider with a
//! user's OWN key: the chat endpoint, the auth-header shape, and a default model.
//! This mirrors (in Rust, for the bot) the declarative `ProviderProfile` the
//! co-developed `hermes-agent` already ships per provider — the bot needs only
//! the thin "endpoint + auth + default model" slice to drive a single chat turn
//! with the user's ported-in key, metered and permissioned by dregg.
//!
//! Two auth shapes cover all five: Anthropic uses `x-api-key` + an
//! `anthropic-version` header against the Messages API; the rest are
//! OpenAI-compatible (`Authorization: Bearer …` against `/chat/completions`).
//!
//! The live HTTP call ([`live_complete`]) is async and used by the channel loop
//! ONLY when the user has set a key and the operator has enabled real calls
//! (`HERMES_LIVE_LLM=1`). All enforcement (budget / rate / provider-permission)
//! is proven offline against a [`MockTransport`] — no paid API calls in tests.

use std::collections::{BTreeMap, BTreeSet};

use crate::key_vault::PlaintextKey;

/// The five providers a user can port a key in for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Provider {
    Anthropic,
    OpenAi,
    OpenRouter,
    /// Kimi (Moonshot AI).
    Kimi,
    DeepSeek,
}

impl Provider {
    /// All providers, for enumeration (pickers, allow-all policies, tests).
    pub const ALL: [Provider; 5] = [
        Provider::Anthropic,
        Provider::OpenAi,
        Provider::OpenRouter,
        Provider::Kimi,
        Provider::DeepSeek,
    ];

    /// The canonical lowercase id (the DB value + the key-vault AAD provider tag).
    pub fn as_str(self) -> &'static str {
        match self {
            Provider::Anthropic => "anthropic",
            Provider::OpenAi => "openai",
            Provider::OpenRouter => "openrouter",
            Provider::Kimi => "kimi",
            Provider::DeepSeek => "deepseek",
        }
    }

    /// Parse a provider id (accepts a few friendly aliases).
    pub fn parse(s: &str) -> Option<Provider> {
        match s.trim().to_ascii_lowercase().as_str() {
            "anthropic" | "claude" => Some(Provider::Anthropic),
            "openai" | "gpt" | "chatgpt" => Some(Provider::OpenAi),
            "openrouter" => Some(Provider::OpenRouter),
            "kimi" | "moonshot" => Some(Provider::Kimi),
            "deepseek" => Some(Provider::DeepSeek),
            _ => None,
        }
    }

    /// A human label for embeds/pickers.
    pub fn display_name(self) -> &'static str {
        match self {
            Provider::Anthropic => "Anthropic (Claude)",
            Provider::OpenAi => "OpenAI",
            Provider::OpenRouter => "OpenRouter",
            Provider::Kimi => "Kimi (Moonshot)",
            Provider::DeepSeek => "DeepSeek",
        }
    }

    /// The chat-completion endpoint URL for this provider.
    pub fn endpoint(self) -> &'static str {
        match self {
            Provider::Anthropic => "https://api.anthropic.com/v1/messages",
            Provider::OpenAi => "https://api.openai.com/v1/chat/completions",
            Provider::OpenRouter => "https://openrouter.ai/api/v1/chat/completions",
            Provider::Kimi => "https://api.moonshot.ai/v1/chat/completions",
            Provider::DeepSeek => "https://api.deepseek.com/v1/chat/completions",
        }
    }

    /// The default model for a freshly-ported key (the user can override).
    pub fn default_model(self) -> &'static str {
        match self {
            // Per the claude-api guidance: default to Claude Opus 4.8.
            Provider::Anthropic => "claude-opus-4-8",
            Provider::OpenAi => "gpt-4o",
            Provider::OpenRouter => "anthropic/claude-opus-4-8",
            Provider::Kimi => "kimi-k2-0905-preview",
            Provider::DeepSeek => "deepseek-chat",
        }
    }

    /// `true` if this provider speaks the Anthropic Messages API (vs the
    /// OpenAI-compatible chat-completions shape the other four use).
    pub fn is_anthropic_messages(self) -> bool {
        matches!(self, Provider::Anthropic)
    }

    /// The auth + protocol headers for a request, given the user's key. Anthropic
    /// uses `x-api-key` + `anthropic-version`; the rest use `Authorization:
    /// Bearer`. Returned as `(name, value)` pairs so the transport sets them
    /// without any provider-specific branching.
    pub fn auth_headers(self, key: &PlaintextKey) -> Vec<(&'static str, String)> {
        match self {
            Provider::Anthropic => vec![
                ("x-api-key", key.expose().to_string()),
                ("anthropic-version", "2023-06-01".to_string()),
            ],
            _ => vec![("authorization", format!("Bearer {}", key.expose()))],
        }
    }
}

/// The result of a completed LLM call — the reply text and the tokens used (for
/// the spend meter). `tokens_used` is the provider's reported usage when
/// available, else an estimate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LlmCompletion {
    pub text: String,
    pub tokens_used: u64,
}

/// What can go wrong calling a provider. Carries NO key material.
#[derive(Clone, Debug)]
pub enum LlmError {
    /// The HTTP request failed (network / non-2xx). The message is the status or
    /// a redacted error — never the key.
    Http(String),
    /// The response could not be parsed into a completion.
    BadResponse(String),
}

impl std::fmt::Display for LlmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LlmError::Http(s) => write!(f, "provider http error: {s}"),
            LlmError::BadResponse(s) => write!(f, "provider response error: {s}"),
        }
    }
}

impl std::error::Error for LlmError {}

/// A coarse token estimate for a piece of text (~4 chars/token), used for the
/// pre-call budget check (the exact count is only known after the call). Min 1.
pub fn estimate_tokens(text: &str) -> u64 {
    ((text.len() as u64) / 4).max(1)
}

/// The policy bounding a user's BYO key-use — the dregg-fit permission layer.
///
/// Three gates, all enforced in-band BEFORE the (paid) provider call:
/// * **provider/model permission** — which providers (and optionally which
///   models) the user is allowed to drive ([`Self::permit`]);
/// * **token/spend budget** — the cumulative token allowance (enforced through
///   the gateway's value-budget [`Charge`](dregg_sdk::Charge); see
///   [`crate::hermes_channel`]);
/// * **rate** — the max LLM calls per session window (the gateway's rate ceiling).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LlmPolicy {
    /// The providers the user may drive. Empty = none permitted (deny-by-default
    /// is the safe posture, but the standard policy permits the user's own set).
    pub allowed_providers: BTreeSet<Provider>,
    /// Optional per-provider model allowlist. `None` for a provider = any model;
    /// `Some(set)` = only those models. Absent provider key = any model.
    pub allowed_models: BTreeMap<Provider, BTreeSet<String>>,
    /// The cumulative TOKEN budget for the session window (the spend cap).
    pub token_budget: u64,
    /// The estimated tokens charged per call against the budget (the gateway's
    /// per-call `price`; the real usage is recorded separately for display).
    pub est_tokens_per_call: u64,
    /// The max number of LLM calls in the session window (the gateway rate).
    pub rate_limit: i64,
}

impl Default for LlmPolicy {
    /// A sensible default: all five providers permitted, any model, a 200k-token
    /// budget at ~2k est/call, 100 calls per window.
    fn default() -> Self {
        LlmPolicy {
            allowed_providers: Provider::ALL.into_iter().collect(),
            allowed_models: BTreeMap::new(),
            token_budget: 200_000,
            est_tokens_per_call: 2_000,
            rate_limit: 100,
        }
    }
}

impl LlmPolicy {
    /// A policy permitting exactly one provider (the user's ported-in one) with
    /// the supplied budget/rate. Any model on that provider is allowed.
    pub fn for_provider(provider: Provider, token_budget: u64, rate_limit: i64) -> Self {
        let mut allowed_providers = BTreeSet::new();
        allowed_providers.insert(provider);
        LlmPolicy {
            allowed_providers,
            allowed_models: BTreeMap::new(),
            token_budget,
            est_tokens_per_call: 2_000,
            rate_limit,
        }
    }

    /// Restrict a provider to a specific model allowlist (chainable).
    pub fn with_models(
        mut self,
        provider: Provider,
        models: impl IntoIterator<Item = String>,
    ) -> Self {
        self.allowed_models
            .insert(provider, models.into_iter().collect());
        self
    }

    /// Whether `(provider, model)` is permitted. Both the provider and (if an
    /// allowlist is set) the model must be allowed.
    pub fn permit(&self, provider: Provider, model: &str) -> Result<(), PermissionDenied> {
        if !self.allowed_providers.contains(&provider) {
            return Err(PermissionDenied::Provider(provider));
        }
        if let Some(models) = self.allowed_models.get(&provider) {
            if !models.is_empty() && !models.contains(model) {
                return Err(PermissionDenied::Model {
                    provider,
                    model: model.to_string(),
                });
            }
        }
        Ok(())
    }
}

/// Why a `(provider, model)` was refused by the policy (the permission gate).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PermissionDenied {
    /// The provider itself is not in the user's allowed set.
    Provider(Provider),
    /// The provider is allowed but the model is not on its allowlist.
    Model { provider: Provider, model: String },
}

impl std::fmt::Display for PermissionDenied {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PermissionDenied::Provider(p) => {
                write!(f, "provider {} is not permitted for this user", p.as_str())
            }
            PermissionDenied::Model { provider, model } => write!(
                f,
                "model {model} is not on the allowlist for {}",
                provider.as_str()
            ),
        }
    }
}

/// A transport that performs the actual completion. The real implementation hits
/// the network; the [`MockTransport`] returns canned output so the enforcement
/// loop is provable offline with no paid API call.
pub trait LlmTransport {
    fn complete(
        &self,
        provider: Provider,
        model: &str,
        key: &PlaintextKey,
        prompt: &str,
    ) -> Result<LlmCompletion, LlmError>;
}

/// A deterministic mock provider for tests — echoes a canned reply and reports a
/// fixed token usage. NEVER touches the network and ignores the key value (it
/// only checks the key is present), so enforcement is proven without secrets.
#[derive(Clone, Debug)]
pub struct MockTransport {
    pub reply: String,
    pub tokens: u64,
}

impl Default for MockTransport {
    fn default() -> Self {
        MockTransport {
            reply: "mock reply".to_string(),
            tokens: 1_500,
        }
    }
}

impl LlmTransport for MockTransport {
    fn complete(
        &self,
        _provider: Provider,
        _model: &str,
        key: &PlaintextKey,
        _prompt: &str,
    ) -> Result<LlmCompletion, LlmError> {
        if key.is_empty() {
            return Err(LlmError::Http("no key".to_string()));
        }
        Ok(LlmCompletion {
            text: self.reply.clone(),
            tokens_used: self.tokens,
        })
    }
}

/// The LIVE provider call (async). Builds the provider-shaped request body, sets
/// the auth + protocol headers from [`Provider::auth_headers`], posts it, and
/// extracts the reply text + token usage. Used only on the gated live path
/// (`HERMES_LIVE_LLM=1` and the user has a key). NEVER called in tests.
pub async fn live_complete(
    client: &reqwest::Client,
    provider: Provider,
    model: &str,
    key: &PlaintextKey,
    prompt: &str,
    max_tokens: u64,
) -> Result<LlmCompletion, LlmError> {
    let body = if provider.is_anthropic_messages() {
        serde_json::json!({
            "model": model,
            "max_tokens": max_tokens,
            "messages": [{"role": "user", "content": prompt}],
        })
    } else {
        serde_json::json!({
            "model": model,
            "max_tokens": max_tokens,
            "messages": [{"role": "user", "content": prompt}],
        })
    };

    let mut req = client.post(provider.endpoint()).json(&body);
    for (name, value) in provider.auth_headers(key) {
        req = req.header(name, value);
    }

    let resp = req
        .send()
        .await
        .map_err(|e| LlmError::Http(redact_reqwest_err(&e)))?;
    let status = resp.status();
    let json: serde_json::Value = resp
        .json()
        .await
        .map_err(|e| LlmError::BadResponse(redact_reqwest_err(&e)))?;
    if !status.is_success() {
        // Surface the provider's error TYPE/status, never the key. Provider
        // error bodies do not echo the request auth header.
        let kind = json
            .get("error")
            .and_then(|e| e.get("type").or_else(|| e.get("message")))
            .and_then(|v| v.as_str())
            .unwrap_or("error");
        return Err(LlmError::Http(format!("{status}: {kind}")));
    }

    extract_completion(provider, &json, prompt)
}

/// Extract the reply text + token usage from a provider response body.
fn extract_completion(
    provider: Provider,
    json: &serde_json::Value,
    prompt: &str,
) -> Result<LlmCompletion, LlmError> {
    let (text, tokens) = if provider.is_anthropic_messages() {
        // Anthropic Messages: content is a list of blocks; concat the text ones.
        let text = json
            .get("content")
            .and_then(|c| c.as_array())
            .map(|blocks| {
                blocks
                    .iter()
                    .filter(|b| b.get("type").and_then(|t| t.as_str()) == Some("text"))
                    .filter_map(|b| b.get("text").and_then(|t| t.as_str()))
                    .collect::<Vec<_>>()
                    .join("")
            })
            .unwrap_or_default();
        let tokens = json
            .get("usage")
            .map(|u| {
                let i = u.get("input_tokens").and_then(|v| v.as_u64()).unwrap_or(0);
                let o = u.get("output_tokens").and_then(|v| v.as_u64()).unwrap_or(0);
                i + o
            })
            .unwrap_or(0);
        (text, tokens)
    } else {
        // OpenAI-compatible: choices[0].message.content + usage.total_tokens.
        let text = json
            .get("choices")
            .and_then(|c| c.as_array())
            .and_then(|a| a.first())
            .and_then(|c| c.get("message"))
            .and_then(|m| m.get("content"))
            .and_then(|t| t.as_str())
            .unwrap_or("")
            .to_string();
        let tokens = json
            .get("usage")
            .and_then(|u| u.get("total_tokens"))
            .and_then(|v| v.as_u64())
            .unwrap_or(0);
        (text, tokens)
    };

    if text.is_empty() {
        return Err(LlmError::BadResponse("empty completion".to_string()));
    }
    let tokens = if tokens == 0 {
        estimate_tokens(prompt) + estimate_tokens(&text)
    } else {
        tokens
    };
    Ok(LlmCompletion {
        text,
        tokens_used: tokens,
    })
}

/// Redact a reqwest error to a loggable string. reqwest errors can carry the URL
/// but never request headers, so the key cannot leak here; we still strip to the
/// status/kind to be conservative.
fn redact_reqwest_err(e: &reqwest::Error) -> String {
    if let Some(status) = e.status() {
        format!("status {status}")
    } else if e.is_timeout() {
        "timeout".to_string()
    } else if e.is_connect() {
        "connection failed".to_string()
    } else if e.is_decode() {
        "decode failed".to_string()
    } else {
        "request failed".to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn providers_round_trip_parse() {
        for p in Provider::ALL {
            assert_eq!(Provider::parse(p.as_str()), Some(p));
        }
        assert_eq!(Provider::parse("claude"), Some(Provider::Anthropic));
        assert_eq!(Provider::parse("moonshot"), Some(Provider::Kimi));
        assert_eq!(Provider::parse("nope"), None);
    }

    #[test]
    fn anthropic_uses_x_api_key_others_bearer() {
        let key = PlaintextKey::new("sk-test-1234");
        let ant = Provider::Anthropic.auth_headers(&key);
        assert!(ant.iter().any(|(n, _)| *n == "x-api-key"));
        assert!(ant.iter().any(|(n, _)| *n == "anthropic-version"));
        // Bearer providers.
        for p in [
            Provider::OpenAi,
            Provider::OpenRouter,
            Provider::Kimi,
            Provider::DeepSeek,
        ] {
            let h = p.auth_headers(&key);
            assert_eq!(h.len(), 1);
            assert_eq!(h[0].0, "authorization");
            assert!(h[0].1.starts_with("Bearer "));
        }
    }

    #[test]
    fn every_provider_has_endpoint_and_default_model() {
        for p in Provider::ALL {
            assert!(p.endpoint().starts_with("https://"));
            assert!(!p.default_model().is_empty());
        }
        assert_eq!(Provider::Anthropic.default_model(), "claude-opus-4-8");
    }

    #[test]
    fn permission_gate_bites_on_provider_and_model() {
        let policy = LlmPolicy::for_provider(Provider::Anthropic, 100_000, 50)
            .with_models(Provider::Anthropic, ["claude-opus-4-8".to_string()]);
        // Allowed provider + allowed model.
        assert!(
            policy
                .permit(Provider::Anthropic, "claude-opus-4-8")
                .is_ok()
        );
        // Allowed provider, disallowed model.
        assert_eq!(
            policy.permit(Provider::Anthropic, "claude-haiku-4-5"),
            Err(PermissionDenied::Model {
                provider: Provider::Anthropic,
                model: "claude-haiku-4-5".to_string()
            })
        );
        // Disallowed provider.
        assert_eq!(
            policy.permit(Provider::OpenAi, "gpt-4o"),
            Err(PermissionDenied::Provider(Provider::OpenAi))
        );
    }

    #[test]
    fn anthropic_response_extraction() {
        let json = serde_json::json!({
            "content": [{"type": "text", "text": "hello world"}],
            "usage": {"input_tokens": 10, "output_tokens": 5}
        });
        let c = extract_completion(Provider::Anthropic, &json, "hi").unwrap();
        assert_eq!(c.text, "hello world");
        assert_eq!(c.tokens_used, 15);
    }

    #[test]
    fn openai_response_extraction() {
        let json = serde_json::json!({
            "choices": [{"message": {"content": "hi there"}}],
            "usage": {"total_tokens": 42}
        });
        let c = extract_completion(Provider::OpenAi, &json, "hi").unwrap();
        assert_eq!(c.text, "hi there");
        assert_eq!(c.tokens_used, 42);
    }

    #[test]
    fn mock_transport_refuses_empty_key() {
        let m = MockTransport::default();
        assert!(
            m.complete(Provider::Kimi, "x", &PlaintextKey::new(""), "p")
                .is_err()
        );
        let ok = m
            .complete(Provider::Kimi, "x", &PlaintextKey::new("sk-real"), "p")
            .unwrap();
        assert_eq!(ok.tokens_used, 1_500);
    }
}
