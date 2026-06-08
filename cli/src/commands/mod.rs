pub mod cap;
pub mod cell;
pub mod cipherclerk;
pub mod directory;
pub mod doctor;
pub mod federation;
pub mod namespace;
pub mod node;
pub mod proof;
pub mod route;
pub mod storage;
pub mod turn;

use crate::config::Config;

/// Build a reqwest client configured for the node.
pub fn http_client() -> reqwest::Client {
    reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(30))
        .build()
        .expect("failed to build HTTP client")
}

/// Construct a full URL for the node API.
pub fn api_url(cfg: &Config, path: &str) -> String {
    let base = cfg.node.url.trim_end_matches('/');
    format!("{base}{path}")
}

/// Attach the configured bearer token to a request, if present. The node's
/// protected endpoints (turn submission, cap ops) require `Authorization:
/// Bearer <token>`; public reads work without it.
fn with_auth(builder: reqwest::RequestBuilder, cfg: &Config) -> reqwest::RequestBuilder {
    match &cfg.node.token {
        Some(t) if !t.is_empty() => builder.bearer_auth(t),
        _ => builder,
    }
}

/// Convenience: GET request to the node, returning JSON value.
pub async fn get_json(
    cfg: &Config,
    path: &str,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    let client = http_client();
    let url = api_url(cfg, path);
    let resp = with_auth(client.get(&url), cfg).send().await?;
    if !resp.status().is_success() {
        let status = resp.status();
        let body = resp.text().await.unwrap_or_default();
        return Err(format!("HTTP {status}: {body}{}", auth_hint(status, cfg)).into());
    }
    let json = resp.json::<serde_json::Value>().await?;
    Ok(json)
}

/// Convenience: POST request with JSON body.
pub async fn post_json(
    cfg: &Config,
    path: &str,
    body: &serde_json::Value,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
    let client = http_client();
    let url = api_url(cfg, path);
    let resp = with_auth(client.post(&url).json(body), cfg).send().await?;
    if !resp.status().is_success() {
        let status = resp.status();
        let text = resp.text().await.unwrap_or_default();
        let hint = if status == reqwest::StatusCode::UNPROCESSABLE_ENTITY {
            " (422: JSON shape mismatch — CLI now emits current node/api.rs request structs; was skew on cell_id/agent/bearer_proof)"
        } else {
            auth_hint(status, cfg)
        };
        return Err(format!("HTTP {status}: {text}{hint}").into());
    }
    let json = resp.json::<serde_json::Value>().await?;
    Ok(json)
}

/// Helpful hint when a protected endpoint rejects an unauthenticated request.
fn auth_hint(status: reqwest::StatusCode, cfg: &Config) -> &'static str {
    if (status == reqwest::StatusCode::UNAUTHORIZED || status == reqwest::StatusCode::FORBIDDEN)
        && cfg.node.token.as_deref().unwrap_or("").is_empty()
    {
        " (this endpoint requires a bearer token — unlock the node and pass --token <bearer_token> \
         from /cipherclerk/unlock, set DREGG_API_TOKEN, or `dregg config set node.token <t>`)"
    } else {
        ""
    }
}
