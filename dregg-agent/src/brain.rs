//! `openai_compat` — a **live LLM brain** behind the Verifiable-Agent-Cloud
//! [`AgentBrain`](crate::agent::AgentBrain) seam, against **any OpenAI-compatible
//! chat/completions endpoint**.
//!
//! The [`agent`](crate::agent) onramp confines an autonomous agent: every
//! decided action is cap-gated, metered, and receipted. The brain that *decides*
//! those actions was, until now, the scripted [`PlannedBrain`](crate::agent::PlannedBrain)
//! (a fixed plan — the mock LLM). [`OpenAICompatBrain`] replaces it with a **real,
//! reactive LLM**: it asks an OpenAI-compatible model — over the chat/completions
//! API with tool-use — for its next move, maps the model's tool-call to an
//! [`AgentAction`](crate::agent::AgentAction), and **observes the gate's verdict**
//! ([`ActionObservation`](crate::agent::ActionObservation)) so the next request
//! reasons over "this tool was refused / this tool returned X". That closed loop —
//!
//! ```text
//!   LLM decides ─▶ (gate: cap ✓ · budget ✓ · receipt) ─▶ observe verdict ─▶ LLM decides …
//! ```
//!
//! IS the agent. The braid around it is unchanged and still the only authority:
//! a tool outside the cap bundle is **refused before it runs** (the model cannot
//! widen its reach by asking), an over-budget call is **bounded in-band** (the
//! LLM's spend has a hard ceiling), and every admitted action is **receipted**
//! (the whole run re-witnesses with [`verify_agent_run`](crate::agent::verify_agent_run)).
//!
//! ## Provider-agnostic: bring any OpenAI-compatible endpoint
//!
//! The chat+tool-use request/response shape (`{messages, tools}` →
//! `choices[].message.tool_calls`) is universal. So the brain is **not** locked to
//! one provider: it takes a configurable **base URL** + **model** + **auth**, and
//! drops in behind any OpenAI-compatible endpoint — a Kimi/Moonshot key, a local
//! proxy, ollama (`http://localhost:11434/v1`), vLLM / LM Studio, OpenRouter
//! (`https://openrouter.ai/api/v1`), or a harness-exposed OpenAI endpoint. The
//! Kimi/Moonshot path is just the historical default (see [`DEFAULT_KIMI_ENDPOINT`]);
//! [`KimiBrain`] / [`LiveKimiCaller`] remain as back-compat aliases.
//!
//! ## The BYO key, confined
//!
//! The model-provider key ([`ProviderKey`]) lives in the brain's pocket and
//! reaches **only** the provider, across the [`OpenAICompatCaller`] seam — it is the
//! `complete` auth argument, never embedded in the request body, a tool-call,
//! a receipt, the run report, or any log. [`ProviderKey`]'s `Debug` is redacted,
//! so even a stray `{:?}` cannot leak it. The key loads from a file (e.g.
//! `~/.kimikey`), an env var, or a raw token; an **unauthenticated** key
//! ([`ProviderKey::unauthenticated`]) is the local-endpoint case (ollama/vLLM with
//! no auth) — no bearer header is sent. dregg never persists the secret.
//!
//! ## The transport seam
//!
//! [`OpenAICompatCaller`] is the one place the key is read and the only thing that
//! touches the network. Two impls ship:
//!   * [`RecordedOpenAICaller`] — replays canned responses (the real OpenAI-style
//!     `choices[].message.tool_calls` shape) for the green tests, records the
//!     base URL + request bodies it was handed (so a test can assert the
//!     configured base/model were used), and **scans every request body for the
//!     key** (a confinement tooth: the key must never appear in what crosses to
//!     the provider as data).
//!   * [`LiveOpenAICompatCaller`] (the `live-brain` feature) — a real
//!     `reqwest::blocking` POST to the configured endpoint, the key in the
//!     `Authorization: Bearer` header (omitted for an unauthenticated key). Off by
//!     default so the std-only green build needs no HTTP stack.

use std::collections::VecDeque;

use serde_json::{Value, json};

use crate::agent::{ActionObservation, AgentAction, AgentBrain};

/// The default Moonshot (Kimi) OpenAI-compatible chat endpoint. Moonshot serves
/// the same API at `api.moonshot.ai` (global) and `api.moonshot.cn` (mainland).
pub const DEFAULT_KIMI_ENDPOINT: &str = "https://api.moonshot.ai/v1/chat/completions";

/// A model id that supports tool-use on the Moonshot API (Kimi's agentic model).
pub const DEFAULT_KIMI_MODEL: &str = "kimi-k2-0711-preview";

/// The OpenAI API base (the `--llm-base` default for `--brain openai`).
pub const DEFAULT_OPENAI_BASE: &str = "https://api.openai.com/v1";

/// The OpenAI chat/completions endpoint (`DEFAULT_OPENAI_BASE` + the chat route).
pub const DEFAULT_OPENAI_ENDPOINT: &str = "https://api.openai.com/v1/chat/completions";

/// Build a chat/completions endpoint URL from a provider **base URL** (the
/// `--llm-base` flag): `http://localhost:11434/v1` → `http://localhost:11434/v1/chat/completions`.
/// A base that already ends in `/chat/completions` is returned unchanged, and a
/// trailing slash on the base is tolerated. This is the one place the OpenAI chat
/// route is appended, so every provider (ollama / vLLM / OpenRouter / a custom
/// proxy) is reached by pointing `--llm-base` at its `/v1`.
pub fn chat_completions_url(base: &str) -> String {
    let base = base.trim_end_matches('/');
    if base.ends_with("/chat/completions") {
        base.to_string()
    } else {
        format!("{base}/chat/completions")
    }
}

// ───────────────────────────── the BYO provider key ─────────────────────────

/// THE OPERATOR'S MODEL-PROVIDER KEY — BYO, held by the brain, confined.
///
/// The secret reaches the provider (the `complete` auth argument) and **nowhere**
/// the agent's reach travels: not the request body, not a tool-call, not a
/// receipt, not the run report, not a log. The redacted [`std::fmt::Debug`] is a
/// confinement tooth — an accidental debug print of a brain holding a key cannot
/// leak it. An [`unauthenticated`](ProviderKey::unauthenticated) key (empty
/// secret) is the local-endpoint case: no bearer header is sent.
#[derive(Clone)]
pub struct ProviderKey {
    provider: String,
    secret: String,
}

impl ProviderKey {
    /// Hold the operator's `secret` for `provider`. The brain is the only holder.
    pub fn new(provider: impl Into<String>, secret: impl Into<String>) -> ProviderKey {
        ProviderKey {
            provider: provider.into(),
            secret: secret.into(),
        }
    }

    /// An **unauthenticated** key — no secret, no bearer header. The local /
    /// unauthed endpoint case (ollama, a local vLLM / LM Studio with auth off).
    pub fn unauthenticated() -> ProviderKey {
        ProviderKey {
            provider: "none".to_string(),
            secret: String::new(),
        }
    }

    /// Load the key from a file (the live deployment shape: `~/.kimikey`). Trailing
    /// whitespace / newline is trimmed. `None` if the file is missing or empty.
    pub fn from_file(
        provider: impl Into<String>,
        path: impl AsRef<std::path::Path>,
    ) -> Option<ProviderKey> {
        let raw = std::fs::read_to_string(path).ok()?;
        let secret = raw.trim();
        if secret.is_empty() {
            return None;
        }
        Some(ProviderKey::new(provider, secret))
    }

    /// Load the key from an environment variable. `None` if unset / empty.
    pub fn from_env(provider: impl Into<String>, var: &str) -> Option<ProviderKey> {
        let secret = std::env::var(var).ok()?;
        if secret.is_empty() {
            return None;
        }
        Some(ProviderKey::new(provider, &secret))
    }

    /// The provider label (NOT secret).
    pub fn provider(&self) -> &str {
        &self.provider
    }

    /// `true` iff this key carries a secret (a bearer token will be sent). `false`
    /// for an [`unauthenticated`](ProviderKey::unauthenticated) local endpoint.
    pub fn is_authenticated(&self) -> bool {
        !self.secret.is_empty()
    }

    /// The secret — readable ONLY to hand to the provider caller. Do not place
    /// the returned string anywhere the agent's reach (the request body / a
    /// tool-call / a receipt / the report) can observe it.
    pub fn secret(&self) -> &str {
        &self.secret
    }
}

impl std::fmt::Debug for ProviderKey {
    /// REDACTED — the secret never prints.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ProviderKey")
            .field("provider", &self.provider)
            .field("secret", &"<redacted>")
            .finish()
    }
}

/// The conventional path of the BYO Kimi key in the operator's home (`~/.kimikey`).
pub fn kimi_key_path() -> Option<std::path::PathBuf> {
    std::env::var_os("HOME").map(|h| std::path::Path::new(&h).join(".kimikey"))
}

/// Load the Kimi key from `~/.kimikey` (the deployment default). `None` if absent.
pub fn kimi_key_from_home() -> Option<ProviderKey> {
    ProviderKey::from_file("moonshot", kimi_key_path()?)
}

// ───────────────────────────── the transport seam ───────────────────────────

/// THE PROVIDER-CALL SEAM — one HTTPS POST to an OpenAI-compatible chat endpoint,
/// the BYO key in hand. The ONLY place the key is read and the ONLY thing that
/// touches the network. A live deployment uses [`LiveOpenAICompatCaller`]; the
/// tests use [`RecordedOpenAICaller`].
pub trait OpenAICompatCaller {
    /// POST `request` to `endpoint` with `api_key` (in the `Authorization: Bearer`
    /// header) and return the provider's raw response JSON.
    ///
    /// `api_key` reaches ONLY here. It must not be embedded in `request` (it goes
    /// in the transport auth header), returned in the response, or logged. An empty
    /// `api_key` means an unauthenticated endpoint — send no bearer header.
    fn complete(&mut self, endpoint: &str, api_key: &str, request: &Value)
    -> Result<Value, String>;
}

/// Back-compat alias: the seam was introduced as `KimiCaller`. Kimi/Moonshot is one
/// OpenAI-compatible endpoint; the seam is now provider-agnostic.
pub use self::OpenAICompatCaller as KimiCaller;

/// A transport that replays canned responses (the real OpenAI-style
/// `{choices:[{message:{tool_calls|content}}]}` shape) — the green-test driver.
///
/// It records the **base URL** ([`endpoints_seen`]) and the **request bodies**
/// ([`requests_seen`]) it was handed, so a test can assert the configured base /
/// model were actually used. It also **scans every request body for the api_key**
/// ([`key_leak_in_body`]): the key must travel in the auth header argument, never
/// as request data. A leak there flips the flag and the key-confinement test fails.
///
/// [`key_leak_in_body`]: RecordedOpenAICaller::key_leak_in_body
/// [`endpoints_seen`]: RecordedOpenAICaller::endpoints_seen
/// [`requests_seen`]: RecordedOpenAICaller::requests_seen
pub struct RecordedOpenAICaller {
    responses: VecDeque<Value>,
    last: Option<Value>,
    repeat_last: bool,
    requests_seen: Vec<Value>,
    endpoints_seen: Vec<String>,
    key_received: bool,
    key_leak_in_body: bool,
}

/// Back-compat alias for [`RecordedOpenAICaller`].
pub type RecordedKimiCaller = RecordedOpenAICaller;

impl RecordedOpenAICaller {
    /// A caller that returns `responses` in order, then errors (the model is
    /// done). Fail-closed: a brain that asks past the script finishes its turn.
    pub fn new(responses: Vec<Value>) -> RecordedOpenAICaller {
        RecordedOpenAICaller {
            responses: responses.into(),
            last: None,
            repeat_last: false,
            requests_seen: Vec::new(),
            endpoints_seen: Vec::new(),
            key_received: false,
            key_leak_in_body: false,
        }
    }

    /// A caller that replays `responses`, then **repeats the last one forever** —
    /// a degenerate model that keeps banging the same tool (a runaway). Used to
    /// show the meter bounds spend regardless of how persistent the model is.
    pub fn repeating(responses: Vec<Value>) -> RecordedOpenAICaller {
        let mut c = RecordedOpenAICaller::new(responses);
        c.repeat_last = true;
        c
    }

    /// `true` once the brain handed a (non-empty) key to this seam — the confined
    /// channel witness (the key DID reach the provider, and only here).
    pub fn key_received(&self) -> bool {
        self.key_received
    }

    /// `true` iff the api_key ever appeared inside a request *body* — a leak. The
    /// confinement invariant requires this to stay `false`.
    pub fn key_leak_in_body(&self) -> bool {
        self.key_leak_in_body
    }

    /// The request bodies the brain sent (for assertions / leak-scanning).
    pub fn requests_seen(&self) -> &[Value] {
        &self.requests_seen
    }

    /// The endpoint (base URL) the brain POSTed to each call — so a test can assert
    /// the configured `--llm-base` was honored, not a hardcoded provider.
    pub fn endpoints_seen(&self) -> &[String] {
        &self.endpoints_seen
    }
}

impl OpenAICompatCaller for RecordedOpenAICaller {
    fn complete(
        &mut self,
        endpoint: &str,
        api_key: &str,
        request: &Value,
    ) -> Result<Value, String> {
        self.requests_seen.push(request.clone());
        self.endpoints_seen.push(endpoint.to_string());
        if !api_key.is_empty() {
            self.key_received = true;
            // CONFINEMENT TOOTH: the key must never ride in the request body.
            if request.to_string().contains(api_key) {
                self.key_leak_in_body = true;
            }
        }
        if let Some(r) = self.responses.pop_front() {
            self.last = Some(r.clone());
            return Ok(r);
        }
        if self.repeat_last {
            if let Some(r) = &self.last {
                return Ok(r.clone());
            }
        }
        Err("no more recorded responses".to_string())
    }
}

/// A real `reqwest::blocking` POST to an OpenAI-compatible endpoint, the BYO key in
/// the `Authorization: Bearer` header (omitted when the key is unauthenticated).
/// Behind the `live-brain` feature so the default std-only build needs no HTTP/TLS
/// stack. Error strings never include the key.
///
/// The blocking request runs on a dedicated OS thread so the caller is agnostic
/// to any ambient async runtime (a `reqwest::blocking` client panics if dropped
/// inside a tokio context — the CLI runs on tokio).
#[cfg(feature = "live-brain")]
#[derive(Default)]
pub struct LiveOpenAICompatCaller;

/// Back-compat alias for [`LiveOpenAICompatCaller`].
#[cfg(feature = "live-brain")]
pub type LiveKimiCaller = LiveOpenAICompatCaller;

#[cfg(feature = "live-brain")]
impl LiveOpenAICompatCaller {
    /// A live caller.
    pub fn new() -> LiveOpenAICompatCaller {
        LiveOpenAICompatCaller
    }
}

#[cfg(feature = "live-brain")]
impl OpenAICompatCaller for LiveOpenAICompatCaller {
    fn complete(
        &mut self,
        endpoint: &str,
        api_key: &str,
        request: &Value,
    ) -> Result<Value, String> {
        let endpoint = endpoint.to_string();
        let api_key = api_key.to_string();
        let request = request.clone();
        // Run the blocking client off any ambient async runtime (its own thread).
        let handle = std::thread::spawn(move || -> Result<Value, String> {
            // A request timeout so a hung / silent endpoint fails CLOSED (the brain
            // ends the turn soundly) instead of wedging the agent forever.
            let client = reqwest::blocking::Client::builder()
                .timeout(std::time::Duration::from_secs(60))
                .build()
                .map_err(|e| format!("llm client build error: {e}"))?;
            let mut builder = client.post(&endpoint).json(&request);
            // An empty key = an unauthenticated endpoint (a local ollama / vLLM):
            // send NO bearer header. Otherwise the key rides ONLY in the header.
            if !api_key.is_empty() {
                builder = builder.bearer_auth(&api_key);
            }
            let resp = builder
                .send()
                // The reqwest error Display does not echo the bearer token; do not add it.
                .map_err(|e| format!("llm http error: {e}"))?;
            let status = resp.status();
            let body: Value = resp.json().map_err(|e| format!("llm decode error: {e}"))?;
            if !status.is_success() {
                let msg = body
                    .get("error")
                    .and_then(|e| e.get("message"))
                    .and_then(|m| m.as_str())
                    .unwrap_or("(no message)");
                return Err(format!("llm http {status}: {msg}"));
            }
            Ok(body)
        });
        handle
            .join()
            .map_err(|_| "llm transport thread panicked".to_string())?
    }
}

// ──────────────────────────────── the brain ─────────────────────────────────

/// An assistant message awaiting the gate's verdict — folded into the running
/// conversation by [`OpenAICompatBrain::observe`] so the next request carries the
/// tool-call and its result.
struct PendingCall {
    assistant: Value,
    tool_call_id: String,
}

/// A LIVE, REACTIVE OpenAI-COMPATIBLE LLM BRAIN behind the [`AgentBrain`] seam.
///
/// On each [`AgentBrain::next_action`] it builds an OpenAI-compatible chat request
/// from the running conversation, calls the configured endpoint over
/// [`OpenAICompatCaller`] with the BYO [`ProviderKey`], and maps the model's first
/// tool-call to an [`AgentAction`]: `invoke{service}` / `cell_write{path,value}` /
/// `cell_read{path}`; a `finish` tool-call or a plain text answer ends the turn. On
/// each [`AgentBrain::observe`] it folds the gate's verdict back into the
/// conversation (`admitted — receipted` / `refused: <reason>`), so the model adapts.
///
/// Fail-closed: a provider error or an unparseable response **finishes** the turn
/// — it never fabricates a tool-call. A `step_cap` bounds the loop so a degenerate
/// model cannot spin forever (the budget bounds *spend*; this bounds *turns*).
pub struct OpenAICompatBrain<C: OpenAICompatCaller> {
    key: ProviderKey,
    endpoint: String,
    model: String,
    caller: C,
    services: Vec<String>,
    cells: Vec<String>,
    /// The running OpenAI conversation (system + user + tool-call/result turns).
    /// The key is NEVER in here.
    messages: Vec<Value>,
    pending: Option<PendingCall>,
    finished: bool,
    step_cap: u64,
    tool_call_seq: u64,
    key_reached_provider: bool,
}

/// Back-compat alias: the brain was introduced as `KimiBrain`. It now drives any
/// OpenAI-compatible endpoint; Kimi/Moonshot is just the historical default.
pub type KimiBrain<C> = OpenAICompatBrain<C>;

impl<C: OpenAICompatCaller> OpenAICompatBrain<C> {
    /// A live brain for `task`, advertising the agent's granted `services` + `cells`
    /// as tools, calling `endpoint` (model `model`) with `key` over `caller`.
    pub fn new(
        task: impl Into<String>,
        services: Vec<String>,
        cells: Vec<String>,
        key: ProviderKey,
        endpoint: impl Into<String>,
        model: impl Into<String>,
        caller: C,
    ) -> OpenAICompatBrain<C> {
        let task = task.into();
        let messages = vec![
            json!({ "role": "system", "content": SYSTEM_PROMPT }),
            json!({ "role": "user", "content": task }),
        ];
        OpenAICompatBrain {
            key,
            endpoint: endpoint.into(),
            model: model.into(),
            caller,
            services,
            cells,
            messages,
            pending: None,
            finished: false,
            step_cap: 32,
            tool_call_seq: 0,
            key_reached_provider: false,
        }
    }

    /// A live brain against the default Moonshot endpoint + Kimi agentic model.
    pub fn with_defaults(
        task: impl Into<String>,
        services: Vec<String>,
        cells: Vec<String>,
        key: ProviderKey,
        caller: C,
    ) -> OpenAICompatBrain<C> {
        OpenAICompatBrain::new(
            task,
            services,
            cells,
            key,
            DEFAULT_KIMI_ENDPOINT,
            DEFAULT_KIMI_MODEL,
            caller,
        )
    }

    /// A live brain against a provider **base URL** (e.g. `http://localhost:11434/v1`
    /// for ollama, `https://openrouter.ai/api/v1`) + a `model` id — the chat route
    /// is appended by [`chat_completions_url`]. The provider-agnostic constructor
    /// the CLI's `--llm-base` / `--llm-model` flags drive.
    pub fn with_base(
        task: impl Into<String>,
        services: Vec<String>,
        cells: Vec<String>,
        key: ProviderKey,
        base: &str,
        model: impl Into<String>,
        caller: C,
    ) -> OpenAICompatBrain<C> {
        OpenAICompatBrain::new(
            task,
            services,
            cells,
            key,
            chat_completions_url(base),
            model,
            caller,
        )
    }

    /// Bound the number of model turns (default 32). The budget bounds *spend*;
    /// this bounds *turns* so a degenerate model cannot loop forever.
    pub fn with_step_cap(mut self, cap: u64) -> OpenAICompatBrain<C> {
        self.step_cap = cap;
        self
    }

    /// The endpoint this brain POSTs to (for display / assertions).
    pub fn endpoint(&self) -> &str {
        &self.endpoint
    }

    /// The model id this brain requests (for display / assertions).
    pub fn model(&self) -> &str {
        &self.model
    }

    /// Whether the BYO key has been handed to the provider caller (and nowhere
    /// else) — the confined-channel witness.
    pub fn key_reached_provider(&self) -> bool {
        self.key_reached_provider
    }

    /// The caller (post-run) — e.g. for a test transport to report what it saw.
    pub fn caller(&self) -> &C {
        &self.caller
    }

    /// The tool specs advertised to the model — the agent's actual cap vocabulary
    /// (the services it may `invoke`, the cells it may read/write), plus `finish`.
    /// The key is not here; the body is safe to witness.
    fn tool_specs(&self) -> Value {
        let mut tools = Vec::new();
        if !self.services.is_empty() {
            tools.push(json!({
                "type": "function",
                "function": {
                    "name": "invoke",
                    "description": "Call one of the agent's granted services/tools \
                                    (run tests, verify a deploy, check health, …).",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "service": { "type": "string", "enum": self.services }
                        },
                        "required": ["service"]
                    }
                }
            }));
        }
        if !self.cells.is_empty() {
            tools.push(json!({
                "type": "function",
                "function": {
                    "name": "cell_write",
                    "description": "Commit a value to one of the agent's cells.",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "path": { "type": "string", "enum": self.cells },
                            "value": { "type": "string" }
                        },
                        "required": ["path", "value"]
                    }
                }
            }));
            tools.push(json!({
                "type": "function",
                "function": {
                    "name": "cell_read",
                    "description": "Read one of the agent's cells.",
                    "parameters": {
                        "type": "object",
                        "properties": {
                            "path": { "type": "string", "enum": self.cells }
                        },
                        "required": ["path"]
                    }
                }
            }));
        }
        tools.push(json!({
            "type": "function",
            "function": {
                "name": "finish",
                "description": "Finish the task with a short summary of what was done.",
                "parameters": {
                    "type": "object",
                    "properties": { "summary": { "type": "string" } }
                }
            }
        }));
        Value::Array(tools)
    }

    /// Build the OpenAI chat request body from the running conversation.
    fn request_body(&self) -> Value {
        json!({
            "model": self.model,
            "messages": self.messages,
            "tools": self.tool_specs(),
            "temperature": 0.3
        })
    }
}

/// The system prompt — frames the model as a confined agent that adapts in-band.
const SYSTEM_PROMPT: &str = "You are a confined dregg agent. You have a budget \
    and a capability bundle. Every tool-call is cap-gated, metered, and receipted; a \
    tool outside your bundle is refused in-band and an exhausted budget bounds you. \
    Use the provided tools to accomplish the task, one call at a time. When a tool is \
    refused, adapt within the capabilities you were granted. Call `finish` when done.";

impl<C: OpenAICompatCaller> AgentBrain for OpenAICompatBrain<C> {
    fn next_action(&mut self, step: u64) -> Option<AgentAction> {
        if self.finished || step >= self.step_cap {
            return None;
        }
        let body = self.request_body();
        // THE ONE PLACE THE BYO KEY IS READ — handed to the caller, in the auth
        // header, never into `body`.
        let resp = match self
            .caller
            .complete(&self.endpoint, self.key.secret(), &body)
        {
            Ok(r) => {
                self.key_reached_provider = true;
                r
            }
            Err(_e) => {
                // Fail-closed: a provider error finishes the turn (no fabricated
                // tool-call). The reason is intentionally not surfaced into the
                // run — it could carry transport detail; the bound/receipt rails
                // are what matters.
                self.finished = true;
                return None;
            }
        };
        self.parse_step(&resp)
    }

    fn observe(&mut self, obs: &ActionObservation) {
        let Some(pending) = self.pending.take() else {
            return;
        };
        // The assistant's tool-call turn, then its result (the gate's verdict) —
        // the reactive feedback the model reasons over next.
        self.messages.push(pending.assistant);
        let content = if obs.admitted {
            match (obs.tool_ok, &obs.tool_summary) {
                (Some(ok), Some(s)) => format!(
                    "admitted (receipted turn); tool verdict={}: {s}",
                    if ok { "pass" } else { "fail" }
                ),
                _ => "admitted (receipted turn)".to_string(),
            }
        } else {
            format!(
                "refused by confinement: {}",
                obs.refusal.as_deref().unwrap_or("(no reason)")
            )
        };
        self.messages.push(json!({
            "role": "tool",
            "tool_call_id": pending.tool_call_id,
            "content": content
        }));
    }
}

impl<C: OpenAICompatCaller> OpenAICompatBrain<C> {
    /// Parse an OpenAI chat response into the next [`AgentAction`], stashing the
    /// assistant turn for [`observe`](OpenAICompatBrain::observe). The first
    /// tool-call wins; a `finish` call or a plain text answer ends the turn
    /// (returns `None`).
    fn parse_step(&mut self, resp: &Value) -> Option<AgentAction> {
        let message = resp
            .get("choices")
            .and_then(|c| c.as_array())
            .and_then(|a| a.first())
            .and_then(|c| c.get("message"));
        let Some(message) = message else {
            // Unparseable — fail-closed.
            self.finished = true;
            return None;
        };

        if let Some(tcs) = message.get("tool_calls").and_then(|t| t.as_array()) {
            if let Some(tc) = tcs.first() {
                let func = tc.get("function");
                let name = func
                    .and_then(|f| f.get("name"))
                    .and_then(|n| n.as_str())
                    .unwrap_or("");
                let args = parse_arguments(func.and_then(|f| f.get("arguments")));
                let tool_call_id = tc
                    .get("id")
                    .and_then(|i| i.as_str())
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| {
                        self.tool_call_seq += 1;
                        format!("tc-{}", self.tool_call_seq)
                    });
                match map_tool_call(name, &args) {
                    Some(action) => {
                        self.pending = Some(PendingCall {
                            assistant: message.clone(),
                            tool_call_id,
                        });
                        return Some(action);
                    }
                    None => {
                        // `finish` (or an unknown tool) — end the turn cleanly.
                        self.messages.push(message.clone());
                        self.finished = true;
                        return None;
                    }
                }
            }
        }

        // No tool-call — a final text answer. End the turn.
        self.messages.push(message.clone());
        self.finished = true;
        None
    }
}

/// Parse an OpenAI tool-call `arguments` field — the API sends it as a JSON
/// *string*, but tolerate an inline object too. Unparseable → `null`.
fn parse_arguments(arguments: Option<&Value>) -> Value {
    match arguments {
        Some(Value::String(s)) => serde_json::from_str(s).unwrap_or(Value::Null),
        Some(v) => v.clone(),
        None => Value::Null,
    }
}

/// Map an OpenAI tool-call name + arguments to an [`AgentAction`]. `None` for
/// `finish` and any unrecognized tool (the turn ends rather than fabricating).
fn map_tool_call(name: &str, args: &Value) -> Option<AgentAction> {
    let s = |k: &str| args.get(k).and_then(|v| v.as_str()).map(|s| s.to_string());
    match name {
        "invoke" => s("service").map(|service| AgentAction::Invoke { service }),
        "cell_write" => match (s("path"), s("value")) {
            (Some(path), Some(value)) => Some(AgentAction::CellWrite { path, value }),
            _ => None,
        },
        "cell_read" => s("path").map(|path| AgentAction::CellRead { path }),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::{AgentCloud, AgentSpec, verify_agent_run};
    use crate::receipt::ChainError;
    use crate::toolkit::{HealthSnapshot, Toolkit};

    /// A fake key for the hermetic tests — distinctive so a leak is unmistakable.
    const TEST_SECRET: &str = "sk-UNITTEST-DONOTLEAK-abcdef0123456789";

    fn test_key() -> ProviderKey {
        ProviderKey::new("moonshot", TEST_SECRET)
    }

    /// An OpenAI response that calls one tool with JSON-string arguments.
    fn oai_tool_call(name: &str, args_json: &str) -> Value {
        json!({
            "choices": [{
                "message": {
                    "role": "assistant",
                    "content": null,
                    "tool_calls": [{
                        "id": format!("call_{name}"),
                        "type": "function",
                        "function": { "name": name, "arguments": args_json }
                    }]
                },
                "finish_reason": "tool_calls"
            }]
        })
    }

    /// An OpenAI final-answer response (no tool-call).
    fn oai_finish(text: &str) -> Value {
        json!({
            "choices": [{
                "message": { "role": "assistant", "content": text },
                "finish_reason": "stop"
            }]
        })
    }

    fn spec(id: &str, budget: i64, services: &[&str], cells: &[&str]) -> AgentSpec {
        let mut s = AgentSpec::new(id, budget);
        s.services = services.iter().map(|s| s.to_string()).collect();
        s.cells = cells.iter().map(|s| s.to_string()).collect();
        s
    }

    fn devops_toolkit() -> Toolkit {
        Toolkit::new()
            .with_check_health("check_health", || {
                HealthSnapshot::healthy("node up · 0 divergence · Σδ=0")
            })
            .with_verify_deploy("verify_deploy", || {
                Ok("served bytes match the committed root".to_string())
            })
    }

    // ── THE LIVE LOOP: the LLM reasons → tool → cap-gated + budget-drawn + receipted ──

    #[test]
    fn kimi_drives_a_cap_gated_metered_receipted_task() {
        let cloud = AgentCloud::from_seed([40u8; 32]);
        let handle = cloud
            .deploy(&spec(
                "agent:kimi-devops",
                10,
                &["check_health", "verify_deploy"],
                &["/deploy"],
            ))
            .unwrap();

        // The model's reasoning, recorded as the real OpenAI tool-call shape:
        //   write the deploy cell → check health → verify the deploy → finish.
        let caller = RecordedKimiCaller::new(vec![
            oai_tool_call(
                "cell_write",
                r#"{"path":"/deploy","value":"site:blog@commit-abc"}"#,
            ),
            oai_tool_call("invoke", r#"{"service":"check_health"}"#),
            oai_tool_call("invoke", r#"{"service":"verify_deploy"}"#),
            oai_finish("Deployed, health green, deploy verified."),
        ]);
        let mut brain = KimiBrain::with_defaults(
            "Deploy the blog, check the node is healthy, and verify the deploy.",
            vec!["check_health".into(), "verify_deploy".into()],
            vec!["/deploy".into()],
            test_key(),
            caller,
        );

        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());

        // The whole sequence ran, was metered, and is receipted.
        assert_eq!(report.admitted, 3, "cell-write + 2 invokes");
        assert_eq!(report.consumed, 3);
        assert_eq!(report.receipts.len(), 3);
        assert_eq!(
            report.cells.get("/deploy"),
            Some(&"site:blog@commit-abc".to_string())
        );
        // The QA/ops verdicts are bound into the receipts and all passed.
        assert!(
            report.all_tools_passed(),
            "QA green: {:?}",
            report.tool_results()
        );
        // The run re-witnesses without trusting the host.
        verify_agent_run(&report).expect("the live-brain run re-witnesses");
        // The key reached the provider seam — and only there.
        assert!(brain.key_reached_provider(), "the key reached the provider");
        assert!(brain.caller().key_received(), "the caller saw the key");
        assert!(
            !brain.caller().key_leak_in_body(),
            "the key never rode in a request body"
        );
    }

    // ── PROVIDER-AGNOSTIC: the configured base URL + model are honored ────────────

    #[test]
    fn the_brain_honors_a_configured_base_url_and_model() {
        let cloud = AgentCloud::from_seed([46u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:byo-llm", 10, &["check_health"], &[]))
            .unwrap();

        // Point the brain at a NON-Moonshot OpenAI-compatible base (ollama-style)
        // with a custom model — neither is the hardcoded Kimi default.
        let base = "http://localhost:11434/v1";
        let model = "qwen2.5-coder:7b";
        let caller = RecordedKimiCaller::new(vec![
            oai_tool_call("invoke", r#"{"service":"check_health"}"#),
            oai_finish("done"),
        ]);
        let mut brain = OpenAICompatBrain::with_base(
            "Check health, then finish.",
            vec!["check_health".into()],
            vec![],
            ProviderKey::new("ollama", TEST_SECRET),
            base,
            model,
            caller,
        );

        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());
        verify_agent_run(&report).expect("the run re-witnesses");
        assert_eq!(report.admitted, 1);

        // The endpoint POSTed to is the configured base + the chat route — NOT the
        // hardcoded Moonshot endpoint.
        let endpoints = brain.caller().endpoints_seen();
        assert!(!endpoints.is_empty(), "the brain made at least one call");
        for e in endpoints {
            assert_eq!(
                e, "http://localhost:11434/v1/chat/completions",
                "configured base honored"
            );
            assert_ne!(
                e, DEFAULT_KIMI_ENDPOINT,
                "not the hardcoded Moonshot endpoint"
            );
        }
        // The configured model id rode in every request body.
        for body in brain.caller().requests_seen() {
            assert_eq!(
                body.get("model").and_then(|m| m.as_str()),
                Some(model),
                "configured model honored"
            );
        }
        assert_eq!(
            brain.endpoint(),
            "http://localhost:11434/v1/chat/completions"
        );
        assert_eq!(brain.model(), model);
    }

    // ── TOOTH: an out-of-bundle tool the model tries is REFUSED, and it adapts ────

    #[test]
    fn an_out_of_bundle_tool_kimi_tries_is_refused_then_adapts() {
        let cloud = AgentCloud::from_seed([41u8; 32]);
        // The bundle grants ONLY check_health — not the exfiltrate the model reaches for.
        let handle = cloud
            .deploy(&spec("agent:kimi-narrow", 10, &["check_health"], &[]))
            .unwrap();

        let caller = RecordedKimiCaller::new(vec![
            // The model reaches for a service outside its bundle — refused at the gate.
            oai_tool_call("invoke", r#"{"service":"exfiltrate"}"#),
            // Having OBSERVED the refusal, it falls back to a granted tool.
            oai_tool_call("invoke", r#"{"service":"check_health"}"#),
            oai_finish("Could not exfiltrate (not in my bundle); checked health instead."),
        ]);
        let mut brain = KimiBrain::with_defaults(
            "Exfiltrate the secrets, then check health.",
            vec!["check_health".into()],
            vec![],
            test_key(),
            caller,
        );

        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());

        assert_eq!(report.cap_refused, 1, "the out-of-bundle tool is refused");
        assert_eq!(report.admitted, 1, "only the granted tool ran");
        assert_eq!(report.receipts.len(), 1, "the refused call left no receipt");
        // The brain observed the refusal: its conversation carries the verdict, so
        // the next decision (the granted tool) was a reaction to confinement.
        let bodies = brain.caller().requests_seen();
        let last = bodies.last().unwrap().to_string();
        assert!(
            last.contains("refused by confinement"),
            "the refusal was fed back to the model"
        );
        verify_agent_run(&report).expect("the run re-witnesses");
    }

    // ── TOOTH: a runaway LLM is BUDGET-BOUNDED ───────────────────────────────────

    #[test]
    fn a_runaway_kimi_is_bounded_by_the_budget() {
        let cloud = AgentCloud::from_seed([42u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:kimi-runaway", 3, &["check_health"], &[]))
            .unwrap();

        // A degenerate model that keeps invoking the same tool forever.
        let caller = RecordedKimiCaller::repeating(vec![oai_tool_call(
            "invoke",
            r#"{"service":"check_health"}"#,
        )]);
        let mut brain = KimiBrain::with_defaults(
            "Check health repeatedly.",
            vec!["check_health".into()],
            vec![],
            test_key(),
            caller,
        )
        .with_step_cap(20);

        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());

        assert_eq!(
            report.admitted, 3,
            "the budget admits exactly budget/cost calls"
        );
        assert_eq!(
            report.budget_refused, 17,
            "the rest are bounded (step_cap 20 − budget 3)"
        );
        assert_eq!(report.consumed, 3, "spend is capped at the ceiling");
        assert_eq!(report.headroom, 0, "the ceiling is fully drawn");
        let v = verify_agent_run(&report).unwrap();
        assert!(v.consumed <= v.budget, "consumed never exceeds the ceiling");
    }

    // ── TOOTH: the BYO key NEVER LEAKS into the report / receipts / wire ──────────

    #[test]
    fn the_byo_key_never_leaks() {
        let cloud = AgentCloud::from_seed([43u8; 32]);
        let handle = cloud
            .deploy(&spec(
                "agent:kimi-confined",
                10,
                &["check_health"],
                &["/deploy"],
            ))
            .unwrap();

        let caller = RecordedKimiCaller::new(vec![
            oai_tool_call("cell_write", r#"{"path":"/deploy","value":"x"}"#),
            oai_tool_call("invoke", r#"{"service":"check_health"}"#),
            oai_finish("done"),
        ]);
        let mut brain = KimiBrain::with_defaults(
            "Deploy and check health.",
            vec!["check_health".into()],
            vec!["/deploy".into()],
            test_key(),
            caller,
        );
        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());

        // The key reached the provider seam (the confined channel) ...
        assert!(brain.key_reached_provider());
        assert!(brain.caller().key_received());
        // ... and NOWHERE the agent's reach travels:
        // (1) not in any request body the brain sent.
        assert!(
            !brain.caller().key_leak_in_body(),
            "key not in any request body"
        );
        for body in brain.caller().requests_seen() {
            assert!(
                !body.to_string().contains(TEST_SECRET),
                "key not in a request body"
            );
        }
        // (2) not in the serialized run report (the proof + bound the user gets).
        let report_json = serde_json::to_string(&report).unwrap();
        assert!(
            !report_json.contains(TEST_SECRET),
            "key not in the run report"
        );
        // (3) not in any individual receipt.
        for r in &report.receipts {
            let rj = serde_json::to_string(r).unwrap();
            assert!(!rj.contains(TEST_SECRET), "key not in a receipt");
        }
        // (4) not in the run log.
        for l in &report.log {
            assert!(
                !format!("{l:?}").contains(TEST_SECRET),
                "key not in the log"
            );
        }
        // (5) a stray Debug of the key is redacted.
        assert!(
            !format!("{:?}", test_key()).contains(TEST_SECRET),
            "Debug is redacted"
        );
        assert!(format!("{:?}", test_key()).contains("<redacted>"));
    }

    // ── a forged QA verdict in a live-brain run still breaks the receipt ──────────

    #[test]
    fn a_forged_verdict_in_a_kimi_run_breaks_the_receipt() {
        let cloud = AgentCloud::from_seed([44u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:kimi-forge", 10, &["check_health"], &[]))
            .unwrap();
        // A snapshot WITH an anomaly → the honest verdict is FAIL.
        let toolkit = Toolkit::new().with_check_health("check_health", || HealthSnapshot {
            divergence: 1,
            ..Default::default()
        });
        let caller = RecordedKimiCaller::new(vec![
            oai_tool_call("invoke", r#"{"service":"check_health"}"#),
            oai_finish("health checked"),
        ]);
        let mut brain = KimiBrain::with_defaults(
            "Check health.",
            vec!["check_health".into()],
            vec![],
            test_key(),
            caller,
        );
        let mut report = cloud.run_with_toolkit(&handle, &mut brain, &toolkit);

        assert!(!report.tool_results()[0].1, "the honest verdict is fail");
        verify_agent_run(&report).expect("the honest fail re-witnesses");

        // Forge the verdict to "passed" → the receipt signature no longer matches.
        report.receipts[0].tool_ok = Some(true);
        assert!(matches!(
            verify_agent_run(&report),
            Err(crate::agent::AgentVerifyError::Chain(
                ChainError::BadSignature { .. }
            ))
        ));
    }

    // ── key loading + the unauthenticated (local-endpoint) case ──────────────────

    #[test]
    fn key_loads_from_a_file_trimmed() {
        let dir = std::env::temp_dir().join(format!("kimi-key-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("kimikey");
        std::fs::write(&path, format!("  {TEST_SECRET}\n")).unwrap();
        let key = ProviderKey::from_file("moonshot", &path).expect("key loads");
        assert_eq!(
            key.secret(),
            TEST_SECRET,
            "trailing whitespace/newline trimmed"
        );
        assert!(key.is_authenticated());
        assert!(
            !format!("{key:?}").contains(TEST_SECRET),
            "redacted under Debug"
        );
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn an_unauthenticated_key_sends_no_secret() {
        let key = ProviderKey::unauthenticated();
        assert!(!key.is_authenticated(), "no secret to send");
        assert_eq!(key.secret(), "", "an empty secret = no bearer header");
        // The recorded caller treats an empty key as "not received" (no confined
        // channel to witness): a local unauthed endpoint.
        let cloud = AgentCloud::from_seed([47u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:local-llm", 10, &["check_health"], &[]))
            .unwrap();
        let caller = RecordedKimiCaller::new(vec![
            oai_tool_call("invoke", r#"{"service":"check_health"}"#),
            oai_finish("done"),
        ]);
        let mut brain = OpenAICompatBrain::with_base(
            "Check health.",
            vec!["check_health".into()],
            vec![],
            key,
            "http://localhost:8000/v1",
            "local-model",
            caller,
        );
        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());
        verify_agent_run(&report).expect("the unauthed run re-witnesses");
        assert_eq!(report.admitted, 1);
        assert!(
            !brain.caller().key_received(),
            "no key was handed to an unauthed endpoint"
        );
    }

    #[test]
    fn chat_completions_url_appends_the_route_idempotently() {
        assert_eq!(
            chat_completions_url("http://localhost:11434/v1"),
            "http://localhost:11434/v1/chat/completions"
        );
        assert_eq!(
            chat_completions_url("http://localhost:11434/v1/"),
            "http://localhost:11434/v1/chat/completions"
        );
        // Already a full chat endpoint → unchanged (no double-append).
        assert_eq!(
            chat_completions_url(DEFAULT_KIMI_ENDPOINT),
            DEFAULT_KIMI_ENDPOINT
        );
        assert_eq!(
            chat_completions_url(DEFAULT_OPENAI_BASE),
            DEFAULT_OPENAI_ENDPOINT
        );
    }

    // ── LIVE: one real Kimi call (ignored; needs ~/.kimikey + network) ───────────

    #[cfg(feature = "live-brain")]
    #[test]
    #[ignore = "hits the live Moonshot API; needs ~/.kimikey + network"]
    fn kimi_live_brain_reasons_over_a_real_call() {
        let key = kimi_key_from_home().expect("~/.kimikey present");
        let cloud = AgentCloud::from_seed([45u8; 32]);
        let handle = cloud
            .deploy(&spec(
                "agent:live-brain",
                6,
                &["check_health", "verify_deploy"],
                &["/deploy"],
            ))
            .unwrap();
        let mut brain = KimiBrain::with_defaults(
            "Check the node is healthy and verify the deploy, then finish.",
            vec!["check_health".into(), "verify_deploy".into()],
            vec!["/deploy".into()],
            key,
            LiveKimiCaller::new(),
        )
        .with_step_cap(8);
        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());

        // Whatever happened on the wire, confinement holds: the run is a sound,
        // re-witnessable, budget-bounded receipt chain (an empty chain — the model
        // never reached an admitted action — re-witnesses too).
        let v = verify_agent_run(&report).expect("the live run re-witnesses");
        assert!(v.consumed <= v.budget, "consumed never exceeds the ceiling");

        // Honest about the two live outcomes:
        if brain.key_reached_provider() {
            // The provider accepted the key and answered — a genuine live loop.
            println!(
                "live Kimi loop: admitted={} consumed={} receipts={}",
                report.admitted,
                report.consumed,
                report.receipts.len()
            );
            assert!(
                report.admitted >= 1,
                "the live model drove at least one admitted action"
            );
        } else {
            // The provider rejected the key (or the network failed): the brain
            // fail-closed — no fabricated action, an empty sound chain. This is the
            // documented state when `~/.kimikey` is not a valid Moonshot key.
            println!("live call did not complete (key rejected / unreachable); brain fail-closed");
            assert_eq!(
                report.admitted, 0,
                "fail-closed: no action without a model answer"
            );
        }
    }
}

// ─────────────────────── LIVE round-trip against a local mock ────────────────
//
// Hermetic proof (no network, no `#[ignore]`) that the LIVE transport
// ([`LiveOpenAICompatCaller`]) honors a CONFIGURABLE base URL end-to-end: a tiny
// in-process OpenAI-compatible server on `127.0.0.1:0` returns canned chat +
// tool_calls; the brain reasons → tool-call → cap-gated + metered + receipted →
// re-witnessed. Proves (a) the configured base is honored (the call reaches our
// local host, not Moonshot), (b) the key rides ONLY in the Authorization header
// (never the body), and (c) a dead endpoint fail-closes. Behind `live-brain` (the
// transport feature).
#[cfg(all(test, feature = "live-brain"))]
mod mock_server_tests {
    use super::*;
    use crate::agent::{AgentCloud, AgentSpec, verify_agent_run};
    use crate::toolkit::{HealthSnapshot, Toolkit};
    use std::io::{Read, Write};
    use std::net::TcpListener;
    use std::sync::{Arc, Mutex};

    const TEST_SECRET: &str = "sk-MOCKSERVER-DONOTLEAK-9876543210";

    /// One request the mock server captured.
    #[derive(Clone)]
    struct Captured {
        path: String,
        authorization: Option<String>,
        body: String,
    }

    fn find_subseq(hay: &[u8], needle: &[u8]) -> Option<usize> {
        hay.windows(needle.len()).position(|w| w == needle)
    }

    fn content_length(head: &str) -> usize {
        head.lines()
            .find(|l| l.to_ascii_lowercase().starts_with("content-length:"))
            .and_then(|l| l[l.find(':').unwrap() + 1..].trim().parse().ok())
            .unwrap_or(0)
    }

    /// Spawn a one-shot-per-connection OpenAI-compatible server that serves
    /// `responses` in order. Returns `(base_url, captured, join_handle)`.
    fn spawn_mock(
        responses: Vec<Value>,
    ) -> (
        String,
        Arc<Mutex<Vec<Captured>>>,
        std::thread::JoinHandle<()>,
    ) {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        let base = format!("http://{addr}/v1");
        let captured: Arc<Mutex<Vec<Captured>>> = Arc::new(Mutex::new(Vec::new()));
        let cap2 = captured.clone();
        let n = responses.len();
        let handle = std::thread::spawn(move || {
            let mut served = 0usize;
            // Accept EXACTLY `n` connections (one POST per canned response), then
            // exit — never block on an (n+1)th accept (which would wedge join()).
            while served < n {
                let mut stream = match listener.accept() {
                    Ok((s, _)) => s,
                    Err(_) => break,
                };
                // Never block forever on a misbehaving client.
                let _ = stream.set_read_timeout(Some(std::time::Duration::from_secs(3)));
                // Read the full request (headers + Content-Length body).
                let mut buf: Vec<u8> = Vec::new();
                let mut tmp = [0u8; 2048];
                let mut header_end: Option<usize> = None;
                let mut clen = 0usize;
                loop {
                    let read = match stream.read(&mut tmp) {
                        Ok(0) | Err(_) => break,
                        Ok(k) => k,
                    };
                    buf.extend_from_slice(&tmp[..read]);
                    if header_end.is_none() {
                        if let Some(pos) = find_subseq(&buf, b"\r\n\r\n") {
                            header_end = Some(pos + 4);
                            let head = String::from_utf8_lossy(&buf[..pos]).to_string();
                            clen = content_length(&head);
                        }
                    }
                    if let Some(he) = header_end {
                        if buf.len() >= he + clen {
                            break;
                        }
                    }
                }
                let he = header_end.unwrap_or(buf.len());
                let head = String::from_utf8_lossy(&buf[..he.saturating_sub(4).min(buf.len())])
                    .to_string();
                let body_end = (he + clen).min(buf.len());
                let body = String::from_utf8_lossy(&buf[he.min(buf.len())..body_end]).to_string();
                let path = head
                    .lines()
                    .next()
                    .unwrap_or("")
                    .split_whitespace()
                    .nth(1)
                    .unwrap_or("")
                    .to_string();
                let authorization = head
                    .lines()
                    .find(|l| l.to_ascii_lowercase().starts_with("authorization:"))
                    .map(|l| l[l.find(':').unwrap() + 1..].trim().to_string());
                cap2.lock().unwrap().push(Captured {
                    path,
                    authorization,
                    body,
                });

                let resp_body = responses[served].to_string();
                served += 1;
                let resp = format!(
                    "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
                    resp_body.len(),
                    resp_body
                );
                let _ = stream.write_all(resp.as_bytes());
                let _ = stream.flush();
            }
        });
        (base, captured, handle)
    }

    fn oai_tool_call(name: &str, args_json: &str) -> Value {
        json!({
            "choices": [{
                "message": {
                    "role": "assistant",
                    "content": null,
                    "tool_calls": [{
                        "id": format!("call_{name}"),
                        "type": "function",
                        "function": { "name": name, "arguments": args_json }
                    }]
                },
                "finish_reason": "tool_calls"
            }]
        })
    }

    fn oai_finish(text: &str) -> Value {
        json!({
            "choices": [{ "message": { "role": "assistant", "content": text }, "finish_reason": "stop" }]
        })
    }

    fn devops_toolkit() -> Toolkit {
        Toolkit::new().with_check_health("check_health", || HealthSnapshot::healthy("node up"))
    }

    fn spec(id: &str, budget: i64, services: &[&str]) -> AgentSpec {
        let mut s = AgentSpec::new(id, budget);
        s.services = services.iter().map(|s| s.to_string()).collect();
        s
    }

    // ── a REAL HTTP round-trip to a CONFIGURABLE base works end-to-end ───────────

    #[test]
    fn live_transport_honors_a_configurable_base_url_end_to_end() {
        // Two canned turns: invoke check_health, then finish.
        let (base, captured, handle) = spawn_mock(vec![
            oai_tool_call("invoke", r#"{"service":"check_health"}"#),
            oai_finish("done"),
        ]);

        let cloud = AgentCloud::from_seed([60u8; 32]);
        let agent = cloud
            .deploy(&spec("agent:mock-llm", 10, &["check_health"]))
            .unwrap();
        let mut brain = OpenAICompatBrain::with_base(
            "Check the node is healthy, then finish.",
            vec!["check_health".into()],
            vec![],
            ProviderKey::new("mock", TEST_SECRET),
            &base,
            "mock-model",
            LiveOpenAICompatCaller::new(),
        )
        .with_step_cap(8);

        let report = cloud.run_with_toolkit(&agent, &mut brain, &devops_toolkit());
        handle.join().ok();

        // The genuine live loop ran: the model drove a real admitted action over HTTP.
        verify_agent_run(&report).expect("the live mock-server run re-witnesses");
        assert!(
            brain.key_reached_provider(),
            "the provider answered over the wire"
        );
        assert_eq!(
            report.admitted, 1,
            "check_health ran, cap-gated + metered + receipted"
        );

        let reqs = captured.lock().unwrap().clone();
        assert!(
            reqs.len() >= 1,
            "the configured local endpoint received the request"
        );
        // (a) the base URL was honored — the request hit OUR local /v1/chat/completions,
        // not the hardcoded Moonshot endpoint.
        for r in &reqs {
            assert_eq!(
                r.path, "/v1/chat/completions",
                "configured base URL honored"
            );
        }
        // (b) the key rode ONLY in the Authorization header, never the request body.
        assert_eq!(
            reqs[0].authorization.as_deref(),
            Some(format!("Bearer {TEST_SECRET}").as_str()),
            "the key reached the provider in the auth header"
        );
        for r in &reqs {
            assert!(
                !r.body.contains(TEST_SECRET),
                "the key never rode in a request body"
            );
        }
        // (c) the key never leaks into the report / receipts.
        let report_json = serde_json::to_string(&report).unwrap();
        assert!(
            !report_json.contains(TEST_SECRET),
            "key not in the run report"
        );
    }

    // ── fail-closed on a dead endpoint (connection refused) ──────────────────────

    #[test]
    fn live_transport_fails_closed_on_a_dead_endpoint() {
        let cloud = AgentCloud::from_seed([61u8; 32]);
        let agent = cloud
            .deploy(&spec("agent:dead-llm", 10, &["check_health"]))
            .unwrap();
        // Port 1 on localhost: nothing listens → connection refused → fail-closed.
        let mut brain = OpenAICompatBrain::with_base(
            "Check health.",
            vec!["check_health".into()],
            vec![],
            ProviderKey::new("mock", TEST_SECRET),
            "http://127.0.0.1:1/v1",
            "mock-model",
            LiveOpenAICompatCaller::new(),
        )
        .with_step_cap(4);

        let report = cloud.run_with_toolkit(&agent, &mut brain, &devops_toolkit());

        // Fail-closed: no fabricated action, an empty but sound + re-witnessable chain.
        let v = verify_agent_run(&report).expect("the empty chain re-witnesses");
        assert_eq!(report.admitted, 0, "no action without a provider answer");
        assert!(v.consumed <= v.budget);
        assert!(
            !brain.key_reached_provider(),
            "the dead endpoint never answered"
        );
    }
}
