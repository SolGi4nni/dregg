//! The [`Narrator`] — three backends and an honest fallback chain.
//!
//! [`Narrator::auto`] resolves, in order: **Bedrock(Claude Haiku 4.5)** → on
//! `BudgetExhausted`/`UnpricedModel`/error → **Bedrock(Nova Lite)** → **Ollama** (if reachable) →
//! **Scripted** (deterministic, no network, no spend). Every produced [`Narration`] reports the
//! `kind` that ACTUALLY narrated — e.g. `model:us.anthropic.claude-haiku-4-5-20251001-v1:0`,
//! `model:gemma2:2b`, `scripted`, or `scripted(budget-exhausted)`. It never names a model that
//! did not run.

use std::sync::Arc;

use crate::backend::{
    metered_converse, ConverseBackend, ConverseMessage, ConverseRequest, ConverseResponse, ToolDef,
};
use crate::bedrock::BedrockClient;
use crate::ledger::BudgetLedger;
use crate::models::{ModelRegistry, CLAUDE_HAIKU_4_5, NOVA_2_LITE};
use crate::ollama::OllamaBackend;
use crate::openai::OpenAiCompatClient;
use crate::NarratorError;

/// A produced narration + the honest kind of what produced it.
#[derive(Clone, Debug)]
pub struct Narration {
    pub text: String,
    /// What ACTUALLY narrated: `model:<id>`, `scripted`, or `scripted(budget-exhausted)`.
    pub kind: String,
}

/// One backend in the fallback chain.
enum Backend {
    /// A hosted, metered model behind a [`ConverseBackend`] (shared client, per-backend model id).
    /// Provider-agnostic: AWS Bedrock (Nova/Claude) or any OpenAI-compatible endpoint (Chutes /
    /// Bittensor, vLLM, OpenRouter, a local proxy) — every call is priced and capped identically.
    Hosted {
        client: Arc<dyn ConverseBackend + Send + Sync>,
        model: String,
    },
    /// A local Ollama model (no spend).
    Ollama(OllamaBackend),
    /// The deterministic offline narrator (no network, no spend).
    Scripted,
}

impl Backend {
    fn kind(&self) -> String {
        match self {
            Backend::Hosted { model, .. } => format!("model:{model}"),
            Backend::Ollama(o) => o.kind(),
            Backend::Scripted => "scripted".to_string(),
        }
    }
}

/// The narrator: an ordered backend chain + the ledger + the price registry.
pub struct Narrator {
    backends: Vec<Backend>,
    ledger: BudgetLedger,
    registry: ModelRegistry,
}

impl Narrator {
    /// The full auto chain: hosted model(s) → Ollama → Scripted. The hosted tier is chosen by
    /// `DREGG_NARRATOR`: `openai`/`chutes` uses the OpenAI-compatible endpoint
    /// (`DREGG_NARRATOR_ENDPOINT` + `DREGG_NARRATOR_MODEL`); `bedrock` (or AWS creds present) uses
    /// Bedrock(Haiku)→Bedrock(Nova), or a single model when `DREGG_NARRATOR_MODEL` is set;
    /// `ollama`/`scripted`/`none` skip the hosted tier. When `DREGG_NARRATOR` is unset, an explicit
    /// `DREGG_NARRATOR_ENDPOINT` selects the OpenAI path, else AWS creds select Bedrock.
    pub fn auto() -> Narrator {
        let mut backends = hosted_and_ollama();
        backends.push(Backend::Scripted);
        Narrator {
            backends,
            ledger: BudgetLedger::from_env(),
            registry: ModelRegistry::builtin(),
        }
    }

    /// The MODEL tier only — the hosted model(s) → Ollama, with NO scripted backend. A caller that
    /// owns its own deterministic fallback (like the dungeon-service) uses this so
    /// [`Narrator::narrate`] returns `Err` when every hosted/local model is unavailable or the
    /// budget is exhausted, and the caller can drop to ITS scripted narration.
    pub fn models_from_env() -> Narrator {
        Narrator {
            backends: hosted_and_ollama(),
            ledger: BudgetLedger::from_env(),
            registry: ModelRegistry::builtin(),
        }
    }

    /// A narrator with an explicit backend set — used by tests to inject fakes.
    pub fn for_test(
        ledger: BudgetLedger,
        registry: ModelRegistry,
        hosted: Vec<(Arc<dyn ConverseBackend + Send + Sync>, String)>,
        ollama: Option<OllamaBackend>,
        scripted: bool,
    ) -> Narrator {
        let mut backends: Vec<Backend> = hosted
            .into_iter()
            .map(|(client, model)| Backend::Hosted { client, model })
            .collect();
        if let Some(o) = ollama {
            backends.push(Backend::Ollama(o));
        }
        if scripted {
            backends.push(Backend::Scripted);
        }
        Narrator {
            backends,
            ledger,
            registry,
        }
    }

    /// The ledger this narrator meters against.
    pub fn ledger(&self) -> &BudgetLedger {
        &self.ledger
    }

    /// The kind of the FIRST backend — an informational boot label (`model:<id>` / `scripted`),
    /// or `None` if there are no backends. Per-call honesty comes from [`Narration::kind`].
    pub fn primary_kind(&self) -> Option<String> {
        self.backends.first().map(Backend::kind)
    }

    /// Narrate: run the chain and return the first backend's text, tagged with what produced it.
    /// A `BudgetExhausted` or `UnpricedModel` or backend error advances to the next backend; a
    /// scripted backend reached AFTER a budget exhaustion reports `scripted(budget-exhausted)`.
    /// `Err` only if the chain is exhausted with no scripted backend.
    pub fn narrate(
        &self,
        system: &str,
        user: &str,
        max_tokens: u32,
    ) -> Result<Narration, NarratorError> {
        let mut budget_exhausted = false;
        let mut last_err: Option<NarratorError> = None;

        for b in &self.backends {
            match b {
                Backend::Hosted { client, model } => {
                    let req = ConverseRequest {
                        model: model.clone(),
                        system: system.to_string(),
                        messages: vec![ConverseMessage::user(user)],
                        max_tokens,
                        tools: Vec::new(),
                    };
                    match metered_converse(&self.ledger, &self.registry, client.as_ref(), &req) {
                        Ok(resp) if !resp.text.trim().is_empty() => {
                            return Ok(Narration {
                                text: resp.text,
                                kind: format!("model:{model}"),
                            })
                        }
                        Ok(_) => last_err = Some(NarratorError::Backend("empty narration".into())),
                        Err(e @ NarratorError::BudgetExhausted { .. }) => {
                            budget_exhausted = true;
                            last_err = Some(e);
                        }
                        Err(e) => last_err = Some(e),
                    }
                }
                Backend::Ollama(o) => {
                    let prompt = fold_prompt(system, user);
                    match o.generate(&prompt) {
                        Ok(text) if !text.trim().is_empty() => {
                            return Ok(Narration {
                                text,
                                kind: o.kind(),
                            })
                        }
                        Ok(_) => last_err = Some(NarratorError::Backend("ollama empty".into())),
                        Err(e) => last_err = Some(NarratorError::Backend(e)),
                    }
                }
                Backend::Scripted => {
                    return Ok(Narration {
                        text: scripted_text(user),
                        kind: if budget_exhausted {
                            "scripted(budget-exhausted)".to_string()
                        } else {
                            "scripted".to_string()
                        },
                    });
                }
            }
        }

        Err(last_err
            .unwrap_or_else(|| NarratorError::AllBackendsFailed("no backends configured".into())))
    }

    /// The tool-calling path — run a full Converse (system + messages + `toolConfig`) against the
    /// Bedrock backends in chain order, returning the raw [`ConverseResponse`] (text AND any tool
    /// calls) plus the `model:<id>` kind that produced it. Ollama/Scripted do not carry tools, so
    /// this is Bedrock-only; `Err` if no Bedrock backend succeeds.
    pub fn converse(
        &self,
        system: &str,
        messages: Vec<ConverseMessage>,
        max_tokens: u32,
        tools: Vec<ToolDef>,
    ) -> Result<(ConverseResponse, String), NarratorError> {
        let mut last_err: Option<NarratorError> = None;
        for b in &self.backends {
            if let Backend::Hosted { client, model } = b {
                let req = ConverseRequest {
                    model: model.clone(),
                    system: system.to_string(),
                    messages: messages.clone(),
                    max_tokens,
                    tools: tools.clone(),
                };
                match metered_converse(&self.ledger, &self.registry, client.as_ref(), &req) {
                    Ok(resp) => return Ok((resp, format!("model:{model}"))),
                    Err(e) => last_err = Some(e),
                }
            }
        }
        Err(last_err.unwrap_or_else(|| {
            NarratorError::AllBackendsFailed("no hosted backend for tool-calling".into())
        }))
    }
}

/// Build the model tier — the hosted backend(s) for the resolved provider followed by a reachable
/// Ollama. Empty if none are available.
fn hosted_and_ollama() -> Vec<Backend> {
    let mut backends: Vec<Backend> = Vec::new();

    match hosted_provider() {
        HostedProvider::OpenAi => {
            // The OpenAI-compatible path (Chutes / Bittensor, vLLM, OpenRouter, a local proxy).
            // A missing endpoint or missing model yields no hosted backend — the chain falls
            // through to Ollama/Scripted rather than failing.
            if let Ok(client) = OpenAiCompatClient::from_env() {
                let shared: Arc<dyn ConverseBackend + Send + Sync> = Arc::new(client);
                for model in openai_models() {
                    backends.push(Backend::Hosted {
                        client: shared.clone(),
                        model,
                    });
                }
            }
        }
        HostedProvider::Bedrock => {
            if let Ok(client) = BedrockClient::from_env() {
                let shared: Arc<dyn ConverseBackend + Send + Sync> = Arc::new(client);
                for model in bedrock_models() {
                    backends.push(Backend::Hosted {
                        client: shared.clone(),
                        model,
                    });
                }
            }
        }
        HostedProvider::None => {}
    }

    if let Some(o) = OllamaBackend::probe_env() {
        backends.push(Backend::Ollama(o));
    }

    backends
}

/// Which hosted provider (if any) the environment selects.
enum HostedProvider {
    /// An OpenAI-compatible endpoint (Chutes / Bittensor, vLLM, OpenRouter, a local proxy).
    OpenAi,
    /// AWS Bedrock (Nova / Claude).
    Bedrock,
    /// No hosted tier — Ollama/Scripted only.
    None,
}

/// Resolve the hosted provider: `DREGG_NARRATOR=openai`/`chutes` → OpenAI-compatible; `=bedrock` →
/// Bedrock; `=ollama`/`scripted`/`none` → none. When unset, an explicit `DREGG_NARRATOR_ENDPOINT`
/// selects the OpenAI path, else present AWS credentials select Bedrock, else none.
fn hosted_provider() -> HostedProvider {
    match std::env::var("DREGG_NARRATOR")
        .ok()
        .as_deref()
        .map(str::trim)
    {
        Some("openai") | Some("chutes") => HostedProvider::OpenAi,
        Some("bedrock") => HostedProvider::Bedrock,
        Some("ollama") | Some("scripted") | Some("none") => HostedProvider::None,
        _ => {
            if std::env::var_os("DREGG_NARRATOR_ENDPOINT").is_some() {
                HostedProvider::OpenAi
            } else if aws_creds_present() {
                HostedProvider::Bedrock
            } else {
                HostedProvider::None
            }
        }
    }
}

/// The OpenAI-compatible model(s) to try: the `DREGG_NARRATOR_MODEL` id. Empty if unset — the
/// OpenAI path has no universal default model id across proxies, so it must be named explicitly
/// (e.g. a Chutes catalog id from `GET https://llm.chutes.ai/v1/models`).
fn openai_models() -> Vec<String> {
    match std::env::var("DREGG_NARRATOR_MODEL") {
        Ok(m) if !m.trim().is_empty() => vec![m.trim().to_string()],
        _ => Vec::new(),
    }
}

/// The Bedrock models to try, in order: a single `DREGG_NARRATOR_MODEL` if set, else the two
/// defaults (Haiku, then the cheap verified Nova Lite).
fn bedrock_models() -> Vec<String> {
    match std::env::var("DREGG_NARRATOR_MODEL") {
        Ok(m) if !m.trim().is_empty() => vec![m.trim().to_string()],
        _ => vec![CLAUDE_HAIKU_4_5.to_string(), NOVA_2_LITE.to_string()],
    }
}

/// A best-effort synchronous check that AWS credentials are configured: an access-key env var, a
/// named profile, or an `~/.aws/{credentials,config}` file. It does not prove the creds WORK — a
/// bad-cred Bedrock backend simply fails on first call and the chain falls through.
fn aws_creds_present() -> bool {
    if std::env::var_os("AWS_ACCESS_KEY_ID").is_some()
        || std::env::var_os("AWS_PROFILE").is_some()
        || std::env::var_os("AWS_ROLE_ARN").is_some()
        || std::env::var_os("AWS_CONTAINER_CREDENTIALS_RELATIVE_URI").is_some()
    {
        return true;
    }
    if let Some(home) = std::env::var_os("HOME") {
        let aws = std::path::Path::new(&home).join(".aws");
        return aws.join("credentials").exists() || aws.join("config").exists();
    }
    false
}

/// Fold system + user into one prompt for a completion backend (Ollama).
fn fold_prompt(system: &str, user: &str) -> String {
    if system.trim().is_empty() {
        user.to_string()
    } else {
        format!("{system}\n\n{user}")
    }
}

/// A deterministic, no-spend narration — the final honest fallback.
fn scripted_text(user: &str) -> String {
    let snippet: String = user.trim().chars().take(80).collect();
    if snippet.is_empty() {
        "The scene holds its breath; the narrator waits.".to_string()
    } else {
        format!("The narrator considers \u{201c}{snippet}\u{201d} and the scene continues.")
    }
}
