//! The OpenAI-compatible `/v1/chat/completions` backend — one [`ConverseBackend`] that speaks the
//! shape every hosted OpenAI-style endpoint serves: OpenAI, vLLM / SGLang, OpenRouter, a local
//! proxy, and — the reason this exists — **Bittensor inference via Chutes** (`https://llm.chutes.ai/v1`,
//! subnet 64), whose models are priced per token in both USD and TAO.
//!
//! It maps the backend-agnostic [`ConverseRequest`] onto an OpenAI chat request (the `system` string
//! becomes a leading `system` message; each [`ConverseMessage`] a `{role, content}` turn; each
//! [`ToolDef`] a `{type:function, function:{…}}` spec) and parses `choices[0]` back — text,
//! `tool_calls`, `finish_reason`, and the `usage` token counts the true-up prices. The BYO API key
//! reaches ONLY the `Authorization: Bearer` header, never the request body.
//!
//! Like [`crate::bedrock::BedrockClient`], `converse` is BLOCKING (`reqwest::blocking`), so it must
//! not run on an async worker thread — callers on a Tokio runtime move it into `spawn_blocking`
//! (the Discord bot's `narrate_room_gated` already does exactly this).

use std::time::Duration;

use serde_json::{json, Value};

use crate::backend::{ConverseBackend, ConverseRequest, ConverseResponse, Role, ToolCall};

/// The default request timeout (seconds) when `DREGG_NARRATOR_HTTP_TIMEOUT_SECS` is unset.
const DEFAULT_TIMEOUT_SECS: u64 = 60;
/// The default sampling temperature when `DREGG_NARRATOR_TEMPERATURE` is unset. Narration wants some
/// variety; the receipt commits whatever text is produced, so determinism is not required here.
const DEFAULT_TEMPERATURE: f32 = 0.7;

/// A client for any OpenAI-compatible chat/completions endpoint.
pub struct OpenAiCompatClient {
    /// The full chat/completions URL (a base like `https://llm.chutes.ai/v1` is normalized here).
    endpoint: String,
    /// The BYO secret, sent ONLY as `Authorization: Bearer <key>`. Empty = no auth header (a local
    /// unauthenticated proxy).
    api_key: String,
    /// Sampling temperature.
    temperature: f32,
    http: reqwest::blocking::Client,
}

impl OpenAiCompatClient {
    /// A client for `base_url` (a base like `.../v1`, or a full `.../v1/chat/completions`) with the
    /// BYO `api_key` (pass `""` for an unauthenticated local endpoint). Uses the default timeout and
    /// temperature.
    pub fn new(base_url: &str, api_key: impl Into<String>) -> Result<OpenAiCompatClient, String> {
        OpenAiCompatClient::with_settings(
            base_url,
            api_key,
            DEFAULT_TEMPERATURE,
            DEFAULT_TIMEOUT_SECS,
        )
    }

    /// A client with explicit temperature and timeout.
    pub fn with_settings(
        base_url: &str,
        api_key: impl Into<String>,
        temperature: f32,
        timeout_secs: u64,
    ) -> Result<OpenAiCompatClient, String> {
        let base = base_url.trim();
        if base.is_empty() {
            return Err("openai backend: empty endpoint (set DREGG_NARRATOR_ENDPOINT)".to_string());
        }
        let http = reqwest::blocking::Client::builder()
            .timeout(Duration::from_secs(timeout_secs))
            .build()
            .map_err(|e| format!("openai backend: build http client: {e}"))?;
        Ok(OpenAiCompatClient {
            endpoint: chat_completions_url(base),
            api_key: api_key.into(),
            temperature,
            http,
        })
    }

    /// Build a client from the environment:
    /// `DREGG_NARRATOR_ENDPOINT` (base URL, required — e.g. `https://llm.chutes.ai/v1`),
    /// `DREGG_NARRATOR_API_KEY` (the Bearer secret, optional for a local endpoint),
    /// `DREGG_NARRATOR_TEMPERATURE` (optional), `DREGG_NARRATOR_HTTP_TIMEOUT_SECS` (optional).
    pub fn from_env() -> Result<OpenAiCompatClient, String> {
        let base = std::env::var("DREGG_NARRATOR_ENDPOINT")
            .map_err(|_| "openai backend: DREGG_NARRATOR_ENDPOINT is not set".to_string())?;
        let api_key = std::env::var("DREGG_NARRATOR_API_KEY").unwrap_or_default();
        let temperature = std::env::var("DREGG_NARRATOR_TEMPERATURE")
            .ok()
            .and_then(|s| s.trim().parse::<f32>().ok())
            .unwrap_or(DEFAULT_TEMPERATURE);
        let timeout_secs = std::env::var("DREGG_NARRATOR_HTTP_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.trim().parse::<u64>().ok())
            .unwrap_or(DEFAULT_TIMEOUT_SECS);
        OpenAiCompatClient::with_settings(&base, api_key, temperature, timeout_secs)
    }

    /// The resolved chat/completions endpoint (for logging/tests).
    pub fn endpoint(&self) -> &str {
        &self.endpoint
    }
}

impl ConverseBackend for OpenAiCompatClient {
    fn converse(&self, req: &ConverseRequest) -> Result<ConverseResponse, String> {
        let body = build_chat_body(req, self.temperature);
        let mut call = self.http.post(&self.endpoint).json(&body);
        if !self.api_key.is_empty() {
            call = call.bearer_auth(&self.api_key);
        }
        let resp = call.send().map_err(|e| format!("openai request: {e}"))?;

        let status = resp.status();
        let text = resp.text().map_err(|e| format!("openai read body: {e}"))?;
        if !status.is_success() {
            let snippet: String = text.chars().take(500).collect();
            return Err(format!("openai HTTP {status}: {snippet}"));
        }
        let value: Value =
            serde_json::from_str(&text).map_err(|e| format!("openai response not JSON: {e}"))?;
        parse_chat_response(&value, req)
    }
}

/// Normalize a provider base URL into a chat/completions URL:
/// `https://llm.chutes.ai/v1` → `https://llm.chutes.ai/v1/chat/completions`. A URL already ending in
/// `/chat/completions` is returned unchanged; a trailing slash is tolerated.
fn chat_completions_url(base: &str) -> String {
    let base = base.trim().trim_end_matches('/');
    if base.ends_with("/chat/completions") {
        base.to_string()
    } else {
        format!("{base}/chat/completions")
    }
}

/// Translate a [`ConverseRequest`] into an OpenAI chat/completions request body. `stream:false` (the
/// metered path reads a single JSON envelope); `tools` is included only when non-empty (some
/// endpoints reject an empty array).
///
/// PUBLIC because the ATTESTED Chutes backend (`dregg-chutes-e2ee`) encrypts exactly this body to
/// a TEE-attested ML-KEM key instead of POSTing it in the clear. Sharing the one mapping is the
/// point: an attested path that re-authored its own request shape would silently drift from the
/// plain path (a mirror, not a backend).
pub fn build_chat_body(req: &ConverseRequest, temperature: f32) -> Value {
    let mut messages: Vec<Value> = Vec::with_capacity(req.messages.len() + 1);
    if !req.system.trim().is_empty() {
        messages.push(json!({ "role": "system", "content": req.system }));
    }
    for m in &req.messages {
        let role = match m.role {
            Role::User => "user",
            Role::Assistant => "assistant",
        };
        messages.push(json!({ "role": role, "content": m.text }));
    }

    let mut body = json!({
        "model": req.model,
        "messages": messages,
        "max_tokens": req.max_tokens,
        "temperature": temperature,
        "stream": false,
    });

    if !req.tools.is_empty() {
        let tools: Vec<Value> = req
            .tools
            .iter()
            .map(|t| {
                json!({
                    "type": "function",
                    "function": {
                        "name": t.name,
                        "description": t.description,
                        "parameters": t.input_schema,
                    }
                })
            })
            .collect();
        body["tools"] = Value::Array(tools);
    }

    body
}

/// Parse an OpenAI chat/completions response envelope into a [`ConverseResponse`]. Handles a string,
/// null, or array-of-parts `content`; maps `tool_calls`; reads `usage.prompt_tokens` /
/// `usage.completion_tokens` for the true-up (falling back to a byte-length estimate only when the
/// provider omits `usage`, so the ledger never silently charges zero for a real call).
///
/// PUBLIC for the same reason as [`build_chat_body`]: the attested Chutes backend decrypts an
/// enclave's reply into this same envelope and parses it with this same function, then sets
/// [`ConverseResponse::attestation`] itself.
pub fn parse_chat_response(
    resp: &Value,
    req: &ConverseRequest,
) -> Result<ConverseResponse, String> {
    // A provider-level error envelope (200 body carrying `{"error": …}`) must not be read as an
    // empty completion.
    if let Some(err) = resp.get("error") {
        let msg = err
            .get("message")
            .and_then(Value::as_str)
            .map(str::to_string)
            .unwrap_or_else(|| err.to_string());
        return Err(format!("openai error envelope: {msg}"));
    }

    let choice = resp
        .get("choices")
        .and_then(Value::as_array)
        .and_then(|a| a.first())
        .ok_or_else(|| "openai response has no choices".to_string())?;
    let message = choice
        .get("message")
        .ok_or_else(|| "openai choice has no message".to_string())?;

    let text = extract_content_text(message.get("content"));

    let mut tool_calls = Vec::new();
    if let Some(calls) = message.get("tool_calls").and_then(Value::as_array) {
        for tc in calls {
            let func = tc.get("function");
            let name = func
                .and_then(|f| f.get("name"))
                .and_then(Value::as_str)
                .unwrap_or("")
                .to_string();
            let input = match func.and_then(|f| f.get("arguments")) {
                Some(Value::String(s)) => serde_json::from_str(s).unwrap_or(Value::Null),
                Some(v) => v.clone(),
                None => Value::Null,
            };
            let id = tc
                .get("id")
                .and_then(Value::as_str)
                .unwrap_or("")
                .to_string();
            tool_calls.push(ToolCall { id, name, input });
        }
    }

    let stop_reason = choice
        .get("finish_reason")
        .and_then(Value::as_str)
        .unwrap_or("")
        .to_string();

    let usage = resp.get("usage");
    let input_tokens = usage
        .and_then(|u| u.get("prompt_tokens"))
        .and_then(Value::as_u64)
        .map(|n| n as u32)
        .unwrap_or_else(|| estimate_tokens(req.prompt_bytes()));
    let output_tokens = usage
        .and_then(|u| u.get("completion_tokens"))
        .and_then(Value::as_u64)
        .map(|n| n as u32)
        .unwrap_or_else(|| estimate_tokens(text.len()));

    Ok(ConverseResponse {
        text,
        tool_calls,
        stop_reason,
        input_tokens,
        output_tokens,
        // Plain (UNATTESTED) OpenAI-compatible inference. An attesting caller
        // (`dregg-chutes-e2ee`'s `ChutesTeeBackend`) reuses this parser and then fills the slot
        // from ITS verification — this function never claims an attestation it did not run.
        attestation: None,
    })
}

/// Pull the assistant text out of an OpenAI `message.content`, which may be a string, `null` (when
/// the turn is a pure tool call), or an array of `{type:"text", text:…}` parts.
fn extract_content_text(content: Option<&Value>) -> String {
    match content {
        Some(Value::String(s)) => s.clone(),
        Some(Value::Array(parts)) => {
            let mut out = String::new();
            for p in parts {
                if let Some(t) = p.get("text").and_then(Value::as_str) {
                    if !out.is_empty() {
                        out.push('\n');
                    }
                    out.push_str(t);
                }
            }
            out
        }
        _ => String::new(),
    }
}

/// A conservative whole-token estimate (≈4 bytes/token, rounded up) used only when the provider
/// omits `usage`. Never used when real counts are present.
fn estimate_tokens(bytes: usize) -> u32 {
    ((bytes as u64).div_ceil(4)).min(u32::MAX as u64) as u32
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::{ConverseMessage, ToolDef};

    #[test]
    fn url_normalization() {
        assert_eq!(
            chat_completions_url("https://llm.chutes.ai/v1"),
            "https://llm.chutes.ai/v1/chat/completions"
        );
        assert_eq!(
            chat_completions_url("https://llm.chutes.ai/v1/"),
            "https://llm.chutes.ai/v1/chat/completions"
        );
        assert_eq!(
            chat_completions_url("https://x/v1/chat/completions"),
            "https://x/v1/chat/completions"
        );
    }

    #[test]
    fn body_has_system_message_and_max_tokens() {
        let req = ConverseRequest::plain("some-model", "You are the DM.", "I open the door.", 256);
        let body = build_chat_body(&req, 0.5);
        assert_eq!(body["model"], "some-model");
        assert_eq!(body["max_tokens"], 256);
        assert_eq!(body["stream"], false);
        let msgs = body["messages"].as_array().unwrap();
        assert_eq!(msgs[0]["role"], "system");
        assert_eq!(msgs[0]["content"], "You are the DM.");
        assert_eq!(msgs[1]["role"], "user");
        assert_eq!(msgs[1]["content"], "I open the door.");
        // No tools key when there are no tools.
        assert!(body.get("tools").is_none());
    }

    /// Multi-turn: assistant turns keep the `assistant` role and the order is preserved (the
    /// attested backend encrypts this exact body, so a role slip would be invisible on the wire).
    #[test]
    fn body_preserves_multi_turn_roles_and_order() {
        let mut req = ConverseRequest::plain("m", "DM rules.", "I open the door.", 128);
        req.messages.push(ConverseMessage::assistant("It resists."));
        req.messages.push(ConverseMessage::user("I shoulder it."));
        let body = build_chat_body(&req, 0.7);
        let msgs = body["messages"].as_array().unwrap();
        let roles: Vec<&str> = msgs.iter().map(|m| m["role"].as_str().unwrap()).collect();
        assert_eq!(roles, ["system", "user", "assistant", "user"]);
        assert_eq!(msgs[3]["content"], "I shoulder it.");
    }

    #[test]
    fn body_maps_tools_with_real_schema() {
        let mut req = ConverseRequest::plain("m", "", "go", 64);
        req.tools = vec![ToolDef {
            name: "move".to_string(),
            description: "move the party".to_string(),
            input_schema: json!({ "type": "object", "properties": { "dir": { "type": "string" } } }),
        }];
        let body = build_chat_body(&req, 0.7);
        let tools = body["tools"].as_array().unwrap();
        assert_eq!(tools[0]["type"], "function");
        assert_eq!(tools[0]["function"]["name"], "move");
        assert_eq!(
            tools[0]["function"]["parameters"]["properties"]["dir"]["type"],
            "string"
        );
    }

    #[test]
    fn parse_plain_completion_with_usage() {
        let req = ConverseRequest::plain("m", "", "hi", 64);
        let resp = json!({
            "choices": [{
                "message": { "role": "assistant", "content": "The torch gutters." },
                "finish_reason": "stop"
            }],
            "usage": { "prompt_tokens": 12, "completion_tokens": 5 }
        });
        let out = parse_chat_response(&resp, &req).unwrap();
        assert_eq!(out.text, "The torch gutters.");
        assert_eq!(out.stop_reason, "stop");
        assert_eq!(out.input_tokens, 12);
        assert_eq!(out.output_tokens, 5);
        assert!(out.tool_calls.is_empty());
    }

    #[test]
    fn parse_tool_call_with_null_content() {
        let req = ConverseRequest::plain("m", "", "go north", 64);
        let resp = json!({
            "choices": [{
                "message": {
                    "role": "assistant",
                    "content": null,
                    "tool_calls": [{
                        "id": "call_1",
                        "type": "function",
                        "function": { "name": "move", "arguments": "{\"dir\":\"north\"}" }
                    }]
                },
                "finish_reason": "tool_calls"
            }],
            "usage": { "prompt_tokens": 8, "completion_tokens": 3 }
        });
        let out = parse_chat_response(&resp, &req).unwrap();
        assert_eq!(out.text, "");
        assert_eq!(out.tool_calls.len(), 1);
        assert_eq!(out.tool_calls[0].id, "call_1");
        assert_eq!(out.tool_calls[0].name, "move");
        assert_eq!(out.tool_calls[0].input["dir"], "north");
    }

    #[test]
    fn parse_array_content_parts() {
        let req = ConverseRequest::plain("m", "", "hi", 64);
        let resp = json!({
            "choices": [{
                "message": {
                    "role": "assistant",
                    "content": [{ "type": "text", "text": "A" }, { "type": "text", "text": "B" }]
                },
                "finish_reason": "stop"
            }],
            "usage": { "prompt_tokens": 1, "completion_tokens": 1 }
        });
        let out = parse_chat_response(&resp, &req).unwrap();
        assert_eq!(out.text, "A\nB");
    }

    #[test]
    fn missing_usage_falls_back_to_estimate_not_zero() {
        let req = ConverseRequest::plain("m", "", "hi", 64);
        let resp = json!({
            "choices": [{
                "message": { "role": "assistant", "content": "0123456789" },
                "finish_reason": "stop"
            }]
        });
        let out = parse_chat_response(&resp, &req).unwrap();
        // 10 bytes → ceil(10/4) = 3 output tokens; never a silent zero.
        assert_eq!(out.output_tokens, 3);
        assert!(out.input_tokens >= 1);
    }

    #[test]
    fn error_envelope_is_an_error_not_empty_text() {
        let req = ConverseRequest::plain("m", "", "hi", 64);
        let resp = json!({ "error": { "message": "model not found", "type": "invalid_request" } });
        let err = parse_chat_response(&resp, &req).unwrap_err();
        assert!(err.contains("model not found"), "got: {err}");
    }
}
