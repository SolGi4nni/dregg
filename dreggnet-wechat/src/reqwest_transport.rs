//! **The reqwest-backed [`HttpPost`] — the ONE place this crate touches the real network.**
//!
//! Everything above the [`HttpPost`] byte seam is pure ([`crate::transport::RawWeChatApi`] composes
//! the `custom/send` URL + JSON body; [`crate::api`] builds the wire request; [`crate::transport::
//! fetch_access_token`] composes the `cgi-bin/token` URL). This module fills the seam with a thin
//! blocking reqwest client so a real deploy can talk to `https://api.weixin.qq.com`. It mirrors the
//! Telegram frontend's `reqwest_transport::ReqwestHttpPost` shape: blocking (WeChat is plain
//! request/response — no long-poll, no tokio) + rustls (no OpenSSL link).
//!
//! Both edges carry a secret in the URL — the `custom/send` URL bears the access-token, the
//! `cgi-bin/token` URL bears the AppSecret — so every error string uses reqwest's `without_url()`:
//! a token or secret must NEVER reach a log line / journal.

use std::time::Duration;

use crate::transport::HttpPost;

/// How long the HTTP client waits for a response. WeChat's `custom/send` and `cgi-bin/token` are
/// ordinary short request/response calls (no long-poll), so a modest timeout is right — a genuinely
/// dead connection errors out instead of hanging.
const HTTP_TIMEOUT: Duration = Duration::from_secs(30);

/// **A blocking reqwest [`HttpPost`]** — POSTs the `custom/send` body and GETs the `cgi-bin/token`
/// endpoint, returning each response body verbatim (the WeChat envelope parser above decides
/// success from `{ errcode, errmsg }` / `{ access_token, … }`). Cheaply [`Clone`] (a reqwest
/// `Client` is an `Arc` inside), so the send and the token fetch share one connection pool.
///
/// Error strings NEVER include the request URL: the `custom/send` URL carries the access-token and
/// the `cgi-bin/token` URL carries the AppSecret, and an error that echoed either would leak it.
#[derive(Clone, Debug)]
pub struct ReqwestHttpPost {
    client: reqwest::blocking::Client,
}

impl ReqwestHttpPost {
    /// A client with the request/response timeout. Errors only if the TLS backend fails to
    /// initialize (a broken build environment, not a runtime condition).
    pub fn new() -> Result<Self, String> {
        let client = reqwest::blocking::Client::builder()
            .timeout(HTTP_TIMEOUT)
            .build()
            .map_err(|e| format!("build the HTTP client: {e}"))?;
        Ok(ReqwestHttpPost { client })
    }
}

impl HttpPost for ReqwestHttpPost {
    fn post_json(&self, url: &str, body: &str) -> Result<String, String> {
        let resp = self
            .client
            .post(url)
            .header(reqwest::header::CONTENT_TYPE, "application/json")
            .body(body.to_string())
            // `without_url()`: the URL embeds the access-token — never let it reach a log line.
            .send()
            .map_err(|e| format!("wechat POST failed: {}", e.without_url()))?;
        resp.text()
            .map_err(|e| format!("read wechat response body: {}", e.without_url()))
    }

    fn get_json(&self, url: &str) -> Result<String, String> {
        let resp = self
            .client
            .get(url)
            // `without_url()`: the `cgi-bin/token` URL embeds the AppSecret — never log it.
            .send()
            .map_err(|e| format!("wechat GET failed: {}", e.without_url()))?;
        resp.text()
            .map_err(|e| format!("read wechat response body: {}", e.without_url()))
    }
}
