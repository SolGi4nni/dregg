//! Instance discovery + model→chute_id resolution — ports of `chutes_e2ee/discovery.py`
//! and the reference `scripts/test_e2e_client.py::discover_instances`.
//!
//! `GET {api_base}/e2e/instances/{chute_id}` (Bearer) →
//!   `{instances:[{instance_id, e2e_pubkey (base64 of raw 1184 bytes), nonces:[opaque
//!    single-use invocation tokens]}], nonce_expires_in}`.
//! `GET {models_base}/v1/models` (Bearer) → `{data:[{id, chute_id}]}` — resolve a model name
//!   to its chute UUID.

use serde::Deserialize;

use crate::error::ClientError;

/// Default E2EE API base (`https://api.chutes.ai`), where discovery + invoke live.
pub const DEFAULT_API_BASE: &str = "https://api.chutes.ai";
/// Default models base (`https://llm.chutes.ai`), where `/v1/models` lives.
pub const DEFAULT_MODELS_BASE: &str = "https://llm.chutes.ai";

/// One E2EE-capable instance of a chute.
#[derive(Debug, Clone, Deserialize)]
pub struct InstanceInfo {
    pub instance_id: String,
    /// Base64 of the raw 1184-byte ML-KEM-768 public key. Hashed AS THIS STRING into the
    /// attestation `report_data` binding (see [`crate::attest`]).
    pub e2e_pubkey: String,
    /// Opaque single-use invocation tokens; one is echoed verbatim as `X-E2E-Nonce`.
    #[serde(default)]
    pub nonces: Vec<String>,
}

/// The discovery response for a chute.
#[derive(Debug, Clone, Deserialize)]
pub struct Instances {
    pub instances: Vec<InstanceInfo>,
    /// Seconds until the returned invocation nonces expire.
    #[serde(default = "default_nonce_expiry")]
    pub nonce_expires_in: u64,
}

fn default_nonce_expiry() -> u64 {
    55
}

impl Instances {
    /// The instance with the given id, if present.
    pub fn by_id(&self, instance_id: &str) -> Option<&InstanceInfo> {
        self.instances.iter().find(|i| i.instance_id == instance_id)
    }
}

#[derive(Debug, Deserialize)]
struct ModelsResponse {
    #[serde(default)]
    data: Vec<ModelEntry>,
}

#[derive(Debug, Deserialize)]
struct ModelEntry {
    id: Option<String>,
    chute_id: Option<String>,
    /// The flat price sheet Chutes serves per model, USD per **1,000,000** tokens.
    #[serde(default)]
    pricing: Option<FlatPricing>,
    /// The nested twin of `pricing`, carrying the same USD figures alongside their TAO
    /// equivalents. Parsed as a fallback so a shape change in one field is not a silent
    /// un-pricing of the model.
    #[serde(default)]
    price: Option<NestedPrice>,
}

/// `{"prompt": 0.104, "completion": 0.416, …}` — USD per 1,000,000 tokens.
#[derive(Debug, Clone, Deserialize)]
struct FlatPricing {
    #[serde(default)]
    prompt: Option<f64>,
    #[serde(default)]
    completion: Option<f64>,
}

/// `{"input": {"usd": 0.104, "tao": …}, "output": {"usd": 0.416, …}}` — same USD numbers.
#[derive(Debug, Clone, Deserialize)]
struct NestedPrice {
    #[serde(default)]
    input: Option<CurrencyPair>,
    #[serde(default)]
    output: Option<CurrencyPair>,
}

#[derive(Debug, Clone, Deserialize)]
struct CurrencyPair {
    #[serde(default)]
    usd: Option<f64>,
}

/// **The provider's OWN published per-token rate for a model**, normalized to the unit the
/// budget ledger prices in (USD per 1,000 tokens).
///
/// This is the answer to "can we do better than an operator-pinned rate?": Chutes' catalog
/// endpoint publishes a machine-readable price per model, so the ledger can charge the
/// provider's own number instead of a hand-set one. See [`model_pricing`] for what that does and
/// does not buy.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ProviderPricing {
    /// USD per 1,000 INPUT (prompt) tokens.
    pub input_per_1k: f64,
    /// USD per 1,000 OUTPUT (completion) tokens.
    pub output_per_1k: f64,
}

/// Chutes publishes catalog prices in **USD per 1,000,000 tokens** (e.g. `Qwen/Qwen3-32B-TEE`
/// at `prompt: 0.104` = $0.104 per million prompt tokens). The ledger meters per 1,000, so
/// every rate read from the catalog is divided by this.
const CHUTES_PRICE_TOKENS: f64 = 1_000.0;

impl ModelEntry {
    /// The USD-per-1k rates this entry publishes, preferring the flat `pricing` block and
    /// falling back to the nested `price.{input,output}.usd`. `None` when neither carries a
    /// usable pair — a partial sheet pins NOTHING rather than charging zero on one axis, which
    /// is the same fail-closed rule `ModelRegistry::apply_price_override` applies.
    fn rates(&self) -> Option<ProviderPricing> {
        let flat = self
            .pricing
            .as_ref()
            .and_then(|p| Some((p.prompt?, p.completion?)));
        let nested = self
            .price
            .as_ref()
            .and_then(|p| Some((p.input.as_ref()?.usd?, p.output.as_ref()?.usd?)));
        let (prompt, completion) = flat.or(nested)?;
        // A non-finite or negative rate is not a price. A rate of exactly 0 is refused too: a
        // free model would make the per-run ceiling unenforceable (every reservation costs
        // nothing, so nothing ever trips), which is the leak the ledger exists to prevent.
        if !prompt.is_finite() || !completion.is_finite() || prompt <= 0.0 || completion <= 0.0 {
            return None;
        }
        Some(ProviderPricing {
            input_per_1k: prompt / CHUTES_PRICE_TOKENS,
            output_per_1k: completion / CHUTES_PRICE_TOKENS,
        })
    }
}

/// `GET {api_base}/e2e/instances/{chute_id}` (Bearer). Fail-closed on any non-2xx.
pub fn discover(
    http: &reqwest::blocking::Client,
    api_base: &str,
    chute_id: &str,
    cpk: &str,
) -> Result<Instances, ClientError> {
    let url = format!(
        "{}/e2e/instances/{}",
        api_base.trim_end_matches('/'),
        chute_id
    );
    let resp = http
        .get(&url)
        .bearer_auth(cpk)
        .send()
        .map_err(ClientError::Http)?;
    let status = resp.status();
    if !status.is_success() {
        let body = resp.text().unwrap_or_default();
        return Err(ClientError::Discovery(format!(
            "GET {url} -> {status}: {}",
            truncate(&body, 300)
        )));
    }
    resp.json::<Instances>().map_err(ClientError::Http)
}

/// Resolve a model name to a chute_id UUID. If `model` already looks like a UUID it is
/// returned as-is (mirroring `discovery.py::_looks_like_uuid`); otherwise it is looked up in
/// `GET {models_base}/v1/models` by the `chute_id` field.
pub fn resolve_chute_id(
    http: &reqwest::blocking::Client,
    models_base: &str,
    model: &str,
    cpk: &str,
) -> Result<String, ClientError> {
    if looks_like_uuid(model) {
        return Ok(model.to_string());
    }
    let url = format!("{}/v1/models", models_base.trim_end_matches('/'));
    let resp = http
        .get(&url)
        .bearer_auth(cpk)
        .send()
        .map_err(ClientError::Http)?;
    let status = resp.status();
    if !status.is_success() {
        let body = resp.text().unwrap_or_default();
        return Err(ClientError::Discovery(format!(
            "GET {url} -> {status}: {}",
            truncate(&body, 300)
        )));
    }
    let models = resp.json::<ModelsResponse>().map_err(ClientError::Http)?;
    for entry in models.data {
        if let (Some(id), Some(chute_id)) = (entry.id, entry.chute_id) {
            if id == model {
                return Ok(chute_id);
            }
        }
    }
    Err(ClientError::ModelNotFound(model.to_string()))
}

/// **Read a model's price straight off the provider's catalog** — `GET {models_base}/v1/models`,
/// the same request [`resolve_chute_id`] already makes, reading the `pricing` block Chutes serves
/// beside `chute_id`.
///
/// `Ok(None)` means the catalog listed the model but published no usable rate pair for it, or did
/// not list it at all. That is NOT an error: the caller's existing operator-pinned rate still
/// applies, and a model with neither stays unpriced and is refused fail-closed by the metered
/// layer. A transport/HTTP failure IS an `Err`, because "the catalog was unreachable" and "the
/// catalog says this model is free" must never look the same.
///
/// **What this buys, exactly.** The rate is the provider's own published number at the moment it
/// was read, so a ledger charging it is charging what Chutes says it charges — a materially
/// better provenance than a hand-typed rate, which is trusted at the operator's discretion and
/// leaks the ceiling outright if it is set below true cost. **What it does not buy:** it is a
/// SNAPSHOT. Chutes can raise a price after this read, and this process would keep metering at
/// the old rate until it is restarted. That residual is real and is recorded on the
/// `PriceSource` the caller stamps, alongside the date it was read.
pub fn model_pricing(
    http: &reqwest::blocking::Client,
    models_base: &str,
    model: &str,
    cpk: &str,
) -> Result<Option<ProviderPricing>, ClientError> {
    let url = format!("{}/v1/models", models_base.trim_end_matches('/'));
    let resp = http
        .get(&url)
        .bearer_auth(cpk)
        .send()
        .map_err(ClientError::Http)?;
    let status = resp.status();
    if !status.is_success() {
        let body = resp.text().unwrap_or_default();
        return Err(ClientError::Discovery(format!(
            "GET {url} -> {status}: {}",
            truncate(&body, 300)
        )));
    }
    let models = resp.json::<ModelsResponse>().map_err(ClientError::Http)?;
    Ok(models
        .data
        .iter()
        .find(|entry| entry.id.as_deref() == Some(model))
        .and_then(ModelEntry::rates))
}

/// `discovery.py::_looks_like_uuid` — 5 hyphen-separated hex groups, 36 chars total.
pub fn looks_like_uuid(s: &str) -> bool {
    let parts: Vec<&str> = s.split('-').collect();
    if parts.len() != 5 || s.len() != 36 {
        return false;
    }
    s.chars().all(|c| c == '-' || c.is_ascii_hexdigit())
}

fn truncate(s: &str, n: usize) -> String {
    if s.len() <= n {
        s.to_string()
    } else {
        format!("{}…", &s[..n])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A VERBATIM entry from `GET https://llm.chutes.ai/v1/models` (captured 2026-07-26) — the
    /// exact envelope the price parse must survive, fields and all.
    const REAL_ENTRY: &str = r#"{
      "object": "list",
      "data": [{
        "id": "Qwen/Qwen3-32B-TEE",
        "root": "Qwen/Qwen3-32B-FP8",
        "price": {
          "input": {"tao": 0.0005268015346133935, "usd": 0.104},
          "output": {"tao": 0.002107206138453574, "usd": 0.416},
          "input_cache_read": {"tao": 0.00026340076730669676, "usd": 0.052}
        },
        "object": "model",
        "parent": null,
        "created": 1785076921,
        "pricing": {"prompt": 0.104, "completion": 0.416, "input_cache_read": 0.052},
        "chute_id": "ac059e33-eb27-541c-b9a9-24b214036475",
        "owned_by": "sglang",
        "quantization": "fp8",
        "max_model_len": 40960,
        "context_length": 40960,
        "input_modalities": ["text"],
        "max_output_length": 40960,
        "output_modalities": ["text"],
        "supported_features": ["json_mode", "tools", "structured_outputs", "reasoning"],
        "confidential_compute": true,
        "supported_sampling_parameters": ["temperature", "top_p"]
      }]
    }"#;

    fn entry(json: &str) -> ModelEntry {
        serde_json::from_str::<ModelsResponse>(json)
            .expect("the catalog envelope parses")
            .data
            .pop()
            .expect("one entry")
    }

    /// **The answer to "is the rate pinnable from the provider?"**: a real `-TEE` catalog entry
    /// carries a machine-readable price, and it reads out as USD per 1,000 tokens.
    ///
    /// The unit is the load-bearing part and it is asserted numerically: Chutes publishes per
    /// MILLION (`prompt: 0.104` is $0.104/M), the ledger meters per THOUSAND, so a factor-of-1000
    /// slip here is a factor-of-1000 hole in the per-run ceiling. `0.104/M` = `0.000104/1k`.
    #[test]
    fn a_real_tee_catalog_entry_prices_in_usd_per_1k() {
        let rates = entry(REAL_ENTRY)
            .rates()
            .expect("the catalog publishes a rate");
        assert!(
            (rates.input_per_1k - 0.000_104).abs() < 1e-12,
            "$0.104 per MILLION prompt tokens is $0.000104 per THOUSAND, got {}",
            rates.input_per_1k
        );
        assert!(
            (rates.output_per_1k - 0.000_416).abs() < 1e-12,
            "$0.416 per MILLION completion tokens is $0.000416 per THOUSAND, got {}",
            rates.output_per_1k
        );
    }

    /// The nested `price.{input,output}.usd` twin carries the same numbers, so losing the flat
    /// `pricing` block does not silently un-price the model.
    #[test]
    fn the_nested_price_block_is_an_equivalent_fallback() {
        let flat_only =
            entry(r#"{"data":[{"id":"m","pricing":{"prompt":1.25,"completion":3.95}}]}"#)
                .rates()
                .unwrap();
        let nested_only =
            entry(r#"{"data":[{"id":"m","price":{"input":{"usd":1.25},"output":{"usd":3.95}}}]}"#)
                .rates()
                .unwrap();
        assert_eq!(flat_only, nested_only);
        assert!((flat_only.input_per_1k - 0.001_25).abs() < 1e-12);
    }

    /// FAIL-CLOSED on a partial or nonsensical sheet: half a price pins NOTHING (it would charge
    /// zero on the missing axis), and a zero/negative/non-finite rate is refused — a rate of zero
    /// makes every reservation free, so the per-run ceiling could never trip.
    #[test]
    fn a_partial_or_zero_rate_pins_nothing() {
        for json in [
            r#"{"data":[{"id":"m"}]}"#,
            r#"{"data":[{"id":"m","pricing":{"prompt":1.0}}]}"#,
            r#"{"data":[{"id":"m","pricing":{"completion":1.0}}]}"#,
            r#"{"data":[{"id":"m","pricing":{"prompt":0.0,"completion":1.0}}]}"#,
            r#"{"data":[{"id":"m","pricing":{"prompt":1.0,"completion":-1.0}}]}"#,
        ] {
            assert!(
                entry(json).rates().is_none(),
                "must not pin a price from {json}"
            );
        }
    }

    /// An unknown field in the catalog envelope does not break the parse (Chutes adds fields), and
    /// the `chute_id` resolution the attestation path depends on still reads off the same entry.
    #[test]
    fn the_catalog_entry_still_carries_the_chute_id_the_attestor_resolves() {
        let e = entry(REAL_ENTRY);
        assert_eq!(e.id.as_deref(), Some("Qwen/Qwen3-32B-TEE"));
        assert_eq!(
            e.chute_id.as_deref(),
            Some("ac059e33-eb27-541c-b9a9-24b214036475")
        );
    }
}
