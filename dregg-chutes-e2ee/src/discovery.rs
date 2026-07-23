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
