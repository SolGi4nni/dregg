//! The Amazon Bedrock (Nova) backend — the Converse API via `aws-sdk-bedrockruntime`, driven
//! synchronously (the fiction engine is sync) on a small owned Tokio runtime.
//!
//! **Model id.** The Nova models require the INFERENCE-PROFILE id, e.g.
//! `us.amazon.nova-2-lite-v1:0`. The bare `amazon.nova-2-lite-v1:0` errors: *"Invocation of
//! model ID … with on-demand throughput isn't supported. Retry your request with the ID or ARN
//! of an inference profile."* Region `us-east-1`.
//!
//! **Credentials.** The standard AWS chain is honored (no profile is hardcoded) — set
//! `AWS_PROFILE` or use the default chain. `AWS_PROFILE=commonquant-ember` works today.

use aws_smithy_types::{Document, Number};
use serde_json::Value;

use crate::backend::{ConverseBackend, ConverseRequest, ConverseResponse, Role, ToolCall};

/// The default region.
pub const DEFAULT_REGION: &str = "us-east-1";

/// A live Bedrock Converse client. Holds an owned multi-thread runtime (so concurrent blocking
/// calls are safe) and the resolved SDK client. It is model-AGNOSTIC — each [`ConverseRequest`]
/// names its own model, so one client serves the whole fallback chain (Haiku → Nova → …).
pub struct BedrockClient {
    runtime: tokio::runtime::Runtime,
    client: aws_sdk_bedrockruntime::Client,
    region: String,
}

impl BedrockClient {
    /// The configured region.
    pub fn region(&self) -> &str {
        &self.region
    }

    /// Build a client from the environment (region `DREGG_NARRATOR_REGION` / `AWS_REGION`,
    /// credentials from the standard chain — no profile is hardcoded). Returns `Err` with a
    /// human-readable reason if the runtime or SDK config cannot be built. This does NOT verify
    /// the credentials actually work — a bad-cred client fails on first call, where the narrator
    /// chain falls back to Ollama/Scripted.
    pub fn from_env() -> Result<BedrockClient, String> {
        let region = std::env::var("DREGG_NARRATOR_REGION")
            .or_else(|_| std::env::var("AWS_REGION"))
            .unwrap_or_else(|_| DEFAULT_REGION.to_string());

        let runtime = tokio::runtime::Builder::new_multi_thread()
            .worker_threads(1)
            .enable_all()
            .build()
            .map_err(|e| format!("tokio runtime: {e}"))?;

        let region_owned = region.clone();
        let config = runtime.block_on(async move {
            aws_config::defaults(aws_config::BehaviorVersion::latest())
                .region(aws_config::Region::new(region_owned))
                .load()
                .await
        });
        let client = aws_sdk_bedrockruntime::Client::new(&config);

        Ok(BedrockClient {
            runtime,
            client,
            region,
        })
    }

    async fn converse_async(&self, req: &ConverseRequest) -> Result<ConverseResponse, String> {
        use aws_sdk_bedrockruntime::types::{
            ContentBlock, ConversationRole, ConverseOutput, InferenceConfiguration, Message,
            SystemContentBlock, Tool, ToolConfiguration, ToolInputSchema, ToolSpecification,
        };

        let mut call = self.client.converse().model_id(&req.model);

        if !req.system.trim().is_empty() {
            call = call.system(SystemContentBlock::Text(req.system.clone()));
        }

        for m in &req.messages {
            let role = match m.role {
                Role::User => ConversationRole::User,
                Role::Assistant => ConversationRole::Assistant,
            };
            let msg = Message::builder()
                .role(role)
                .content(ContentBlock::Text(m.text.clone()))
                .build()
                .map_err(|e| format!("message build: {e}"))?;
            call = call.messages(msg);
        }

        call = call.inference_config(
            InferenceConfiguration::builder()
                .max_tokens(req.max_tokens as i32)
                .build(),
        );

        if !req.tools.is_empty() {
            let mut tc = ToolConfiguration::builder();
            for t in &req.tools {
                let spec = ToolSpecification::builder()
                    .name(t.name.clone())
                    .description(t.description.clone())
                    .input_schema(ToolInputSchema::Json(value_to_document(&t.input_schema)))
                    .build()
                    .map_err(|e| format!("tool spec build: {e}"))?;
                tc = tc.tools(Tool::ToolSpec(spec));
            }
            let tc = tc.build().map_err(|e| format!("tool config build: {e}"))?;
            call = call.tool_config(tc);
        }

        let out = call
            .send()
            .await
            .map_err(|e| format!("converse: {}", aws_err(&e)))?;

        let stop_reason = out.stop_reason().as_str().to_string();
        let usage = out.usage();
        let input_tokens = usage.map(|u| u.input_tokens()).unwrap_or(0).max(0) as u32;
        let output_tokens = usage.map(|u| u.output_tokens()).unwrap_or(0).max(0) as u32;

        let mut text = String::new();
        let mut tool_calls = Vec::new();
        if let Some(ConverseOutput::Message(msg)) = out.output() {
            for block in msg.content() {
                match block {
                    ContentBlock::Text(t) => {
                        if !text.is_empty() {
                            text.push('\n');
                        }
                        text.push_str(t);
                    }
                    ContentBlock::ToolUse(tu) => {
                        tool_calls.push(ToolCall {
                            id: tu.tool_use_id().to_string(),
                            name: tu.name().to_string(),
                            input: document_to_value(tu.input()),
                        });
                    }
                    _ => {}
                }
            }
        }

        Ok(ConverseResponse {
            text,
            tool_calls,
            stop_reason,
            input_tokens,
            output_tokens,
            // Bedrock is not an attested path — say so honestly rather than leaving it ambiguous.
            attestation: None,
        })
    }
}

impl ConverseBackend for BedrockClient {
    fn converse(&self, req: &ConverseRequest) -> Result<ConverseResponse, String> {
        self.runtime.block_on(self.converse_async(req))
    }
}

/// Pull a legible message out of an SDK error — the service detail when present, else the full
/// source chain (a bare "dispatch failure" is useless without its cause).
fn aws_err<E: std::error::Error + 'static>(
    e: &aws_sdk_bedrockruntime::error::SdkError<E>,
) -> String {
    use aws_sdk_bedrockruntime::error::SdkError;
    if let SdkError::ServiceError(se) = e {
        return format!("{}", se.err());
    }
    let mut msg = format!("{e}");
    let mut src = std::error::Error::source(e);
    while let Some(s) = src {
        msg.push_str(&format!(" -> {s}"));
        src = s.source();
    }
    msg
}

/// Convert a `serde_json::Value` (a JSON-Schema fragment) into a smithy [`Document`].
fn value_to_document(v: &Value) -> Document {
    match v {
        Value::Null => Document::Null,
        Value::Bool(b) => Document::Bool(*b),
        Value::Number(n) => {
            if let Some(u) = n.as_u64() {
                Document::Number(Number::PosInt(u))
            } else if let Some(i) = n.as_i64() {
                Document::Number(Number::NegInt(i))
            } else {
                Document::Number(Number::Float(n.as_f64().unwrap_or(0.0)))
            }
        }
        Value::String(s) => Document::String(s.clone()),
        Value::Array(a) => Document::Array(a.iter().map(value_to_document).collect()),
        Value::Object(o) => Document::Object(
            o.iter()
                .map(|(k, val)| (k.clone(), value_to_document(val)))
                .collect(),
        ),
    }
}

/// Convert a smithy [`Document`] (a tool's input) back into a `serde_json::Value`.
fn document_to_value(d: &Document) -> Value {
    match d {
        Document::Null => Value::Null,
        Document::Bool(b) => Value::Bool(*b),
        Document::Number(n) => match n {
            Number::PosInt(u) => Value::from(*u),
            Number::NegInt(i) => Value::from(*i),
            Number::Float(f) => serde_json::Number::from_f64(*f)
                .map(Value::Number)
                .unwrap_or(Value::Null),
        },
        Document::String(s) => Value::String(s.clone()),
        Document::Array(a) => Value::Array(a.iter().map(document_to_value).collect()),
        Document::Object(o) => Value::Object(
            o.iter()
                .map(|(k, val)| (k.clone(), document_to_value(val)))
                .collect(),
        ),
    }
}
