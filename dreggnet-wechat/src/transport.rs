//! **The INJECTED transport seam** — the ONLY thing that touches the network. All frontend logic
//! (identity, Surface→numbered reply, reply→Action) is built against this trait, so it is fully
//! driven in a test with [`MockTransport`]: NO access-token, NO network. This mirrors the telegram
//! frontend's pure/live split — the [`crate::api`] request builders are pure; a `Transport` is the
//! live edge.
//!
//! Two levels of injection are provided:
//! - [`Transport`] — the logic seam. [`MockTransport`] records every [`CustomSendRequest`] and
//!   acknowledges success; the driven test asserts against the recorded requests.
//! - [`HttpPost`] — the byte seam under the live [`RawWeChatApi`]: `RawWeChatApi` still does PURE
//!   work (compose the `custom/send?access_token=…` URL + the JSON body) and delegates only the raw
//!   POST to an injected [`HttpPost`]. A real deploy supplies a reqwest-backed `HttpPost` + a valid
//!   access-token; a test could supply a recording `HttpPost`. So even the "live" client stays
//!   token/network-free until its byte seam is filled (honest scope).

use crate::api::CustomSendRequest;

/// A transport error (a WeChat API error, a network failure, or a mock-configured failure).
#[derive(Debug, Clone)]
pub struct TransportError(pub String);

impl std::fmt::Display for TransportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "wechat transport error: {}", self.0)
    }
}

impl std::error::Error for TransportError {}

/// **The transport seam.** Sends a [`CustomSendRequest`] to WeChat. Unlike Telegram's `sendMessage`
/// (which returns a `message_id`), WeChat's `custom/send` returns only `{errcode, errmsg}` — there
/// is no server message id to edit later — so a successful send is just `Ok(())`. Frontend logic is
/// generic over this; the test drives it with [`MockTransport`].
pub trait Transport {
    /// Send a `custom/send` request. `Ok(())` on `errcode == 0`; `Err` otherwise.
    fn send_message(&mut self, req: &CustomSendRequest) -> Result<(), TransportError>;
}

/// **A recording, network-free transport** — the frontend-agnostic proof for WeChat. It records
/// every [`CustomSendRequest`] it was asked to send (so a test asserts the exact request shape:
/// touser, msgtype, the numbered-reply text content) and acknowledges success. NO access-token, NO
/// HTTP — the same role [`dreggnet_offerings::mock::MockFrontend`] plays for the core, one layer
/// down at the transport.
#[derive(Debug, Default)]
pub struct MockTransport {
    /// Every request sent, in order (the wire bodies a live OA would POST).
    pub sent: Vec<CustomSendRequest>,
    /// If set, the next `send_message` fails with this reason (to drive the error path).
    fail_next: Option<String>,
}

impl MockTransport {
    /// A fresh recording transport with nothing sent.
    pub fn new() -> Self {
        MockTransport {
            sent: Vec::new(),
            fail_next: None,
        }
    }

    /// The last request sent, if any (the current surface a session shows).
    pub fn last(&self) -> Option<&CustomSendRequest> {
        self.sent.last()
    }

    /// Arm the next `send_message` to fail (drives the [`TransportError`] path in a test).
    pub fn fail_next(&mut self, why: impl Into<String>) {
        self.fail_next = Some(why.into());
    }
}

impl Transport for MockTransport {
    fn send_message(&mut self, req: &CustomSendRequest) -> Result<(), TransportError> {
        if let Some(why) = self.fail_next.take() {
            return Err(TransportError(why));
        }
        self.sent.push(req.clone());
        Ok(())
    }
}

/// **The raw byte seam under the live client.** A live [`RawWeChatApi`] composes the request URL +
/// JSON body purely, and delegates only the raw POST (and the token GET) to this. The crate ships a
/// reqwest-backed impl ([`crate::reqwest_transport::ReqwestHttpPost`]); a test supplies a recording
/// double, so the whole logic layer above stays token/network-free.
///
/// Both methods carry secrets in the URL — `post_json`'s `custom/send` URL bears the access-token,
/// `get_json`'s `cgi-bin/token` URL bears the AppSecret — so a live impl MUST NOT echo the URL in an
/// error string (reqwest's `without_url()`), or it leaks the token/secret into logs.
pub trait HttpPost {
    /// POST `body` (a JSON string) to `url`; return the response body (JSON) or an error string.
    fn post_json(&self, url: &str, body: &str) -> Result<String, String>;

    /// GET `url`, returning the response body (JSON) or an error string. WeChat's access-token
    /// endpoint (`cgi-bin/token`) is a GET, so the ONE injected byte seam covers both the token
    /// fetch and the message send.
    fn get_json(&self, url: &str) -> Result<String, String>;
}

/// **A WeChat Official Account's app credentials** — the AppID + AppSecret from the OA admin
/// console, the root of the access-token fetch. Supplied at DEPLOY from config/env (never checked
/// in); [`from_env`](Self::from_env) is FAIL-CLOSED — an absent key is an `Err`, never a silent
/// empty token. The AppSecret is held private and never surfaced by [`Debug`] (it would leak into
/// logs). It is the *only* thing that cannot be exercised in-tree: it names a real registered OA.
#[derive(Clone)]
pub struct WeChatCredentials {
    /// The OA AppID (public-ish; identifies the account).
    pub app_id: String,
    /// The OA AppSecret — private; used only to build the token-fetch URL in this module.
    app_secret: String,
}

impl std::fmt::Debug for WeChatCredentials {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Never render the AppSecret.
        f.debug_struct("WeChatCredentials")
            .field("app_id", &self.app_id)
            .field("app_secret", &"<redacted>")
            .finish()
    }
}

impl WeChatCredentials {
    /// The env key for the OA AppID.
    pub const APP_ID_KEY: &'static str = "WECHAT_APP_ID";
    /// The env key for the OA AppSecret.
    pub const APP_SECRET_KEY: &'static str = "WECHAT_APP_SECRET";

    /// Credentials from an explicit AppID + AppSecret.
    pub fn new(app_id: impl Into<String>, app_secret: impl Into<String>) -> Self {
        WeChatCredentials {
            app_id: app_id.into(),
            app_secret: app_secret.into(),
        }
    }

    /// Load credentials through an injected key→value lookup (the pure, testable form of
    /// [`from_env`](Self::from_env)). FAIL-CLOSED: a missing OR empty [`APP_ID_KEY`](Self::APP_ID_KEY)
    /// / [`APP_SECRET_KEY`](Self::APP_SECRET_KEY) is an `Err` naming the missing key — never a silent
    /// empty credential.
    pub fn from_lookup(get: impl Fn(&str) -> Option<String>) -> Result<Self, TransportError> {
        let want = |key: &str| -> Result<String, TransportError> {
            get(key)
                .filter(|v| !v.is_empty())
                .ok_or_else(|| TransportError(format!("missing WeChat config: {key}")))
        };
        let app_id = want(Self::APP_ID_KEY)?;
        let app_secret = want(Self::APP_SECRET_KEY)?;
        Ok(WeChatCredentials::new(app_id, app_secret))
    }

    /// Load credentials from the process environment (`WECHAT_APP_ID` / `WECHAT_APP_SECRET`).
    /// FAIL-CLOSED on an absent/empty key (see [`from_lookup`](Self::from_lookup)).
    pub fn from_env() -> Result<Self, TransportError> {
        Self::from_lookup(|key| std::env::var(key).ok())
    }
}

/// **A fetched OA access token + its lifetime.** WeChat access-tokens expire (`expires_in`, usually
/// 7200s); a deploy caches this and re-fetches before it lapses — the refresh timer belongs to the
/// deploy runtime, not this pure layer.
#[derive(Debug, Clone)]
pub struct AccessToken {
    /// The bearer token a [`RawWeChatApi`] carries as the `custom/send` query param.
    pub token: String,
    /// Seconds until the token expires (WeChat's `expires_in`).
    pub expires_in_secs: u64,
}

/// The `cgi-bin/token` URL (pure). Carries the AppSecret, so it is never logged (the [`HttpPost`]
/// contract forbids echoing the URL on error).
fn token_fetch_url(base_url: &str, creds: &WeChatCredentials) -> String {
    format!(
        "{}/cgi-bin/token?grant_type=client_credential&appid={}&secret={}",
        base_url, creds.app_id, creds.app_secret
    )
}

/// **Fetch an OA access token** for `creds` through the injected byte seam `http` (a GET to
/// `cgi-bin/token`). Parses `{ access_token, expires_in }` on success, or the WeChat error envelope
/// `{ errcode, errmsg }` on failure. With a real AppID/AppSecret this returns a LIVE token that
/// [`RawWeChatApi::new`] then bears; with a recording double it returns whatever the stub scripts —
/// so the whole token→send flow is driven with no network.
pub fn fetch_access_token<H: HttpPost>(
    http: &H,
    base_url: &str,
    creds: &WeChatCredentials,
) -> Result<AccessToken, TransportError> {
    let url = token_fetch_url(base_url, creds);
    let resp = http.get_json(&url).map_err(TransportError)?;
    let v: serde_json::Value = serde_json::from_str(&resp)
        .map_err(|e| TransportError(format!("decode WeChat token response: {e}")))?;
    if let Some(token) = v.get("access_token").and_then(|t| t.as_str()) {
        let expires_in_secs = v.get("expires_in").and_then(|e| e.as_u64()).unwrap_or(7200);
        return Ok(AccessToken {
            token: token.to_string(),
            expires_in_secs,
        });
    }
    let errcode = v.get("errcode").and_then(|c| c.as_i64()).unwrap_or(-1);
    let errmsg = v
        .get("errmsg")
        .and_then(|m| m.as_str())
        .unwrap_or("no access_token in the token response");
    Err(TransportError(format!(
        "token fetch failed: errcode {errcode}: {errmsg}"
    )))
}

/// **A live-shaped WeChat API client** — composes the real `https://api.weixin.qq.com/cgi-bin/
/// message/custom/send?access_token=<TOKEN>` URL and the JSON body (both PURE), then delegates the
/// raw POST to an injected [`HttpPost`]. It parses the WeChat envelope (`{ errcode, errmsg }`).
/// Backed by [`crate::reqwest_transport::ReqwestHttpPost`] + an access-token this is a WORKING
/// outbound transport: [`connect`](Self::connect) fetches a token from [`WeChatCredentials`] and
/// builds one in a single step. The access-token itself comes from `cgi-bin/token`
/// ([`fetch_access_token`]) with the OA AppID/AppSecret and is refreshed before its `expires_in`
/// lapses — the refresh timer is the deploy runtime's job.
pub struct RawWeChatApi<H: HttpPost> {
    access_token: String,
    base_url: String,
    http: H,
}

impl<H: HttpPost> RawWeChatApi<H> {
    /// A live client bearing `access_token`, POSTing through `http`. `base_url` defaults to the
    /// public WeChat API host; a proxy / test double passes its own.
    pub fn new(access_token: impl Into<String>, http: H) -> Self {
        RawWeChatApi {
            access_token: access_token.into(),
            base_url: "https://api.weixin.qq.com".to_string(),
            http,
        }
    }

    /// Override the WeChat API host (a proxy, or a test double).
    pub fn with_base_url(mut self, base_url: impl Into<String>) -> Self {
        self.base_url = base_url.into();
        self
    }

    /// **The ordinary deploy path** — fetch an access token from `creds` (through `http`) and build
    /// a live client over the same `http`, in one step. `base_url` is the WeChat API host
    /// (`https://api.weixin.qq.com` in production; a test double passes its own). Fails closed if the
    /// token fetch fails (bad AppID/AppSecret → the WeChat error envelope surfaced verbatim).
    pub fn connect(
        base_url: impl Into<String>,
        creds: &WeChatCredentials,
        http: H,
    ) -> Result<Self, TransportError> {
        let base_url = base_url.into();
        let token = fetch_access_token(&http, &base_url, creds)?;
        Ok(RawWeChatApi {
            access_token: token.token,
            base_url,
            http,
        })
    }

    /// The `custom/send` endpoint URL (pure). Token-bearing (the access-token is a query param, as
    /// WeChat requires), so kept private-ish to this client.
    fn custom_send_url(&self) -> String {
        format!(
            "{}/cgi-bin/message/custom/send?access_token={}",
            self.base_url, self.access_token
        )
    }
}

impl<H: HttpPost> Transport for RawWeChatApi<H> {
    fn send_message(&mut self, req: &CustomSendRequest) -> Result<(), TransportError> {
        let url = self.custom_send_url();
        let body = serde_json::to_string(req)
            .map_err(|e| TransportError(format!("encode custom/send body: {e}")))?;
        let resp = self.http.post_json(&url, &body).map_err(TransportError)?;
        // The WeChat envelope: { "errcode": 0, "errmsg": "ok" }. A missing errcode is treated as
        // success (some endpoints omit it on ok); a non-zero errcode is the error.
        let v: serde_json::Value = serde_json::from_str(&resp)
            .map_err(|e| TransportError(format!("decode WeChat response: {e}")))?;
        let errcode = v.get("errcode").and_then(|c| c.as_i64()).unwrap_or(0);
        if errcode != 0 {
            let errmsg = v
                .get("errmsg")
                .and_then(|m| m.as_str())
                .unwrap_or("WeChat returned a non-zero errcode");
            return Err(TransportError(format!("errcode {errcode}: {errmsg}")));
        }
        Ok(())
    }
}
