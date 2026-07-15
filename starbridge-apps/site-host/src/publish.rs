//! The site-publish control plane — `POST /v1/sites/<name>/publish`.
//!
//! ```text
//!   POST /v1/sites/<name>/publish                (cap-gated, lease-funded, receipted)
//!     headers: Authorization: Bearer dga1_…      (site-host/<name> cap)
//!     body:    a serialized SiteContent (the built bundle, path -> asset)
//!        │  1. authorize  — verify the dga1_ cap -> the owner subject (hard 401 if
//!        │                  the subject cannot be extracted; never a magic fallback)
//!        │  2. rate-limit — per-owner publish ceiling (429)
//!        │  3. quota      — body / asset / count / total bounds (413)
//!        │  4. fund       — a resident non-lapsed hosting lease covers AND is CHARGED
//!        │                  (else 402 + an x402 topup hint to auto-fund + retry)
//!        │  5. publish    — SiteRegistry::publish -> SiteCell + signed receipt
//!        ▼
//!     201 { published, name, owner, content_root, url, signer, receipt }
//!
//!   DELETE /v1/sites/<name>/publish              (cap + owner-gated unpublish)
//!     -> 200 { unpublished, name, receipt }  (a signed delete tombstone)
//! ```
//!
//! [`SitePublishHandler::respond`] is the ONE value-level turn both a CLI
//! ([`crate::cli`]) and an HTTP gateway ([`crate::gateway`]) drive — no HTTP-server
//! types in the core.

use std::sync::Arc;

use dregg_agent::cred::{Credential, PublicKey};
use serde::Serialize;
use webauth_core::grant::cap_context;
use webauth_core::subject_of;

use crate::funding::{FundingDecision, PublishFunding};
use crate::limits::{PublishLimits, RateLimiter};
use crate::registry::{HostConfig, PUBLISH_CAP_PREFIX, PublishCap, PublishError, SiteRegistry};
use crate::site::SiteContent;

/// The value-level HTTP method the control plane accepts (no server-crate types).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HttpMethod {
    Get,
    Post,
    Delete,
    Other,
}

impl HttpMethod {
    /// Parse an HTTP method token (case-insensitive) — for a gateway adapter.
    pub fn parse(s: &str) -> HttpMethod {
        match s.to_ascii_uppercase().as_str() {
            "GET" => HttpMethod::Get,
            "POST" => HttpMethod::Post,
            "DELETE" => HttpMethod::Delete,
            _ => HttpMethod::Other,
        }
    }
}

/// A value-level HTTP response: status, content-type, headers, body. Header-carrying
/// (unlike a bare body-only response) so the funding refusal can emit the x402
/// `X-Payment-Required` header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WebResponse {
    pub status: u16,
    pub content_type: String,
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

impl WebResponse {
    /// A `text/plain` error response with `status` and `msg`.
    pub fn error(status: u16, msg: impl Into<String>) -> WebResponse {
        WebResponse {
            status,
            content_type: "text/plain; charset=utf-8".to_string(),
            headers: Vec::new(),
            body: msg.into().into_bytes(),
        }
    }

    /// An `application/json` response from a serializable value. A serialization
    /// failure surfaces a real `500` (never a silent empty `{}` with a success
    /// status — the output edge does not lie).
    pub fn json(status: u16, value: &impl Serialize) -> WebResponse {
        match serde_json::to_vec(value) {
            Ok(body) => WebResponse {
                status,
                content_type: "application/json".to_string(),
                headers: Vec::new(),
                body,
            },
            Err(e) => WebResponse::error(500, format!("response serialization failed: {e}")),
        }
    }

    /// The body as a UTF-8 string (lossy) — for logging/tests.
    pub fn body_str(&self) -> String {
        String::from_utf8_lossy(&self.body).into_owned()
    }
}

/// The site-publish control plane: writes a built bundle into `registry`, gated on a
/// `site-host/<name>` credential verified under `auth_root`, funded against
/// `funding`, and bounded by quotas + an optional rate limiter.
pub struct SitePublishHandler {
    registry: Arc<SiteRegistry>,
    /// The root authority a presented `dga1_` credential must chain to. `None` =
    /// no root configured -> every publish fails closed (`401`).
    auth_root: Option<PublicKey>,
    /// The funding gate. `None` = no funding configured -> publishes fail closed
    /// (`402`), the no-free-resource posture.
    funding: Option<Arc<dyn PublishFunding>>,
    /// Host config (the parameterized apex the success URL is built from).
    config: HostConfig,
    /// The endpoint a client funds a hosting lease at (echoed into topup hints).
    topup_endpoint: String,
    /// Size quotas enforced on every publish (the DoS guard).
    limits: PublishLimits,
    /// An optional per-owner publish-rate limiter (`None` = unlimited frequency).
    rate_limiter: Option<Arc<RateLimiter>>,
}

impl SitePublishHandler {
    /// A handler publishing into `registry`, verifying credentials under `root`, and
    /// funding against `funding`, serving under `config`, with default quotas and no
    /// rate limiter.
    pub fn new(
        registry: Arc<SiteRegistry>,
        root: Option<PublicKey>,
        funding: Option<Arc<dyn PublishFunding>>,
        config: HostConfig,
    ) -> SitePublishHandler {
        SitePublishHandler {
            registry,
            auth_root: root,
            funding,
            config,
            topup_endpoint: "/v1/leases/topup".to_string(),
            limits: PublishLimits::default(),
            rate_limiter: None,
        }
    }

    /// Override the funding top-up endpoint advertised in x402 hints.
    pub fn with_topup_endpoint(mut self, endpoint: impl Into<String>) -> SitePublishHandler {
        self.topup_endpoint = endpoint.into();
        self
    }

    /// Override the size quotas.
    pub fn with_limits(mut self, limits: PublishLimits) -> SitePublishHandler {
        self.limits = limits;
        self
    }

    /// Attach a per-owner publish-rate limiter.
    pub fn with_rate_limiter(mut self, limiter: Arc<RateLimiter>) -> SitePublishHandler {
        self.rate_limiter = Some(limiter);
        self
    }

    /// The registry this handler publishes into (the inspection surface).
    pub fn registry(&self) -> &Arc<SiteRegistry> {
        &self.registry
    }

    /// Whether this handler serves `path`: a `/v1/sites/<name>/publish`.
    pub fn serves_path(path: &str) -> bool {
        let p = path.split('?').next().unwrap_or(path);
        p.starts_with("/v1/sites/") && p.ends_with("/publish")
    }

    /// The `<name>` a `/v1/sites/<name>/publish` path targets, if well-formed.
    fn name_from_path(path: &str) -> Option<&str> {
        let p = path.split('?').next().unwrap_or(path);
        let rest = p.strip_prefix("/v1/sites/")?;
        let name = rest.strip_suffix("/publish")?;
        if name.is_empty() || name.contains('/') {
            return None;
        }
        Some(name)
    }

    /// Route + serve one publish request as a value response (no HTTP-server types).
    /// `credential` is the presented `dga1_…` token, `now` the verifier's clock.
    pub fn respond(
        &self,
        method: HttpMethod,
        target: &str,
        credential: Option<&str>,
        body: &[u8],
        now: u64,
    ) -> WebResponse {
        let Some(name) = Self::name_from_path(target) else {
            return WebResponse::error(404, "not a site-publish path");
        };
        match method {
            HttpMethod::Post => self.do_publish(name, target, credential, body, now),
            HttpMethod::Delete => self.do_unpublish(name, credential, now),
            _ => WebResponse::error(
                405,
                "publish is POST, unpublish is DELETE, on /v1/sites/<name>/publish",
            ),
        }
    }

    fn do_publish(
        &self,
        name: &str,
        target: &str,
        credential: Option<&str>,
        body: &[u8],
        now: u64,
    ) -> WebResponse {
        // (0) Body-size quota BEFORE the expensive decode — the OOM guard.
        if let Err(q) = self.limits.check_body(body.len()) {
            return WebResponse::error(413, q.to_string());
        }

        // (1) cap-gate: the presented dga1_ credential must carry site-host/<name>.
        let cap = match self.authorize(name, credential, now) {
            Ok(c) => c,
            Err(deny) => return deny,
        };

        // (2) rate-limit per authenticated owner (before charging funding).
        if let Some(rl) = &self.rate_limiter {
            if let Err(retry_after) = rl.check(&cap.holder, now) {
                let mut resp = WebResponse::error(
                    429,
                    format!("publish rate limit exceeded for `{}`", cap.holder),
                );
                resp.headers
                    .push(("Retry-After".to_string(), retry_after.to_string()));
                return resp;
            }
        }

        // (3) funding gate: a resident, non-lapsed hosting lease must cover AND be
        //     charged. A refusal carries the x402 topup hint (auto-fund + retry).
        if let Err(deny) = self.fund(&cap.holder, now, target) {
            return deny;
        }

        // (4) decode the built bundle.
        let content: SiteContent = match serde_json::from_slice(body) {
            Ok(c) => c,
            Err(e) => {
                return WebResponse::error(
                    400,
                    format!("publish body is not a JSON SiteContent bundle: {e}"),
                );
            }
        };

        // (5) content quotas (per-asset / count / total).
        if let Err(q) = self.limits.check_content(&content) {
            return WebResponse::error(413, q.to_string());
        }

        // (6) publish (cap-gated + receipted, durable).
        match self.registry.publish(&cap, name, content) {
            Ok(receipt) => {
                let signer = self.registry.receipt_signer().map(hex32);
                let value = serde_json::json!({
                    "published": true,
                    "name": receipt.name,
                    "owner": receipt.owner,
                    "content_root": receipt.content_root,
                    "asset_count": receipt.asset_count,
                    "url": self.config.url_for(&receipt.name),
                    "signer": signer,
                    "receipt": receipt,
                });
                WebResponse::json(201, &value)
            }
            Err(e) => publish_error_response(e),
        }
    }

    fn do_unpublish(&self, name: &str, credential: Option<&str>, now: u64) -> WebResponse {
        let cap = match self.authorize(name, credential, now) {
            Ok(c) => c,
            Err(deny) => return deny,
        };
        match self.registry.unpublish(&cap, name) {
            Ok(receipt) => {
                let signer = self.registry.receipt_signer().map(hex32);
                let value = serde_json::json!({
                    "unpublished": true,
                    "name": receipt.name,
                    "signer": signer,
                    "receipt": receipt,
                });
                WebResponse::json(200, &value)
            }
            Err(e) => publish_error_response(e),
        }
    }

    /// Verify the presented credential authorizes publishing `name`, returning the
    /// [`PublishCap`] (holder = the credential's stable subject) or the refusal
    /// (`401`/`403`).
    fn authorize(
        &self,
        name: &str,
        credential: Option<&str>,
        now: u64,
    ) -> Result<PublishCap, WebResponse> {
        let Some(root) = &self.auth_root else {
            return Err(WebResponse::error(401, "site cap-authority not configured"));
        };
        let Some(enc) = credential else {
            return Err(WebResponse::error(
                401,
                format!("no credential presented to publish site `{name}`"),
            ));
        };
        let cred = Credential::decode(enc)
            .map_err(|e| WebResponse::error(401, format!("credential did not decode: {e}")))?;
        let required = format!("{PUBLISH_CAP_PREFIX}{name}");
        let ctx = cap_context(&required, now);
        cred.verify(root, &ctx)
            .map_err(|r| WebResponse::error(403, format!("cap `{required}` refused: {r}")))?;
        // The subject MUST resolve after a successful verify: a hard 401, never a
        // magic `dregg:unknown` fallback that would collapse distinct principals into
        // one owner + one funding bucket.
        let Some(holder) = subject_of(enc) else {
            return Err(WebResponse::error(
                401,
                "credential verified but carries no extractable subject",
            ));
        };
        Ok(PublishCap {
            holder,
            cap: required,
        })
    }

    /// The funding gate: admit only against a resident non-lapsed hosting lease, and
    /// CHARGE the accept path. `Ok(())` admits; an `Err` is the `402` refusal (with
    /// the x402 topup hint) to return as-is. `now` drives the clock-driven lapse.
    fn fund(&self, owner: &str, now: u64, retry: &str) -> Result<(), WebResponse> {
        let Some(funding) = &self.funding else {
            return Err(WebResponse::error(
                402,
                "no funding gate configured: refusing to publish without a covering hosting lease",
            ));
        };
        match funding.authorize_publish(owner, now, retry, &self.topup_endpoint) {
            FundingDecision::Covered => Ok(()),
            FundingDecision::Denied(hint) => {
                // x402-style 402: a JSON body with an `accepts` payment-requirement
                // array + the `X-Payment-Required` header, so a machine client reads
                // the requirement, funds the lease, and re-POSTs the publish.
                let value = serde_json::json!({
                    "error": hint.detail,
                    "accepts": [hint],
                });
                let mut resp = WebResponse::json(402, &value);
                resp.headers
                    .push(("X-Payment-Required".to_string(), hint.scheme.clone()));
                Err(resp)
            }
        }
    }
}

/// Extract a `dga1_…` credential from HTTP-style headers: `Authorization: Bearer
/// <tok>` or `X-Dregg-Credential: <tok>`. A helper for an HTTP gateway adapter.
pub fn bearer_credential<'a>(header: impl Fn(&str) -> Option<&'a str>) -> Option<String> {
    if let Some(auth) = header("authorization") {
        let auth = auth.trim();
        if let Some(tok) = auth
            .strip_prefix("Bearer ")
            .or_else(|| auth.strip_prefix("bearer "))
        {
            return Some(tok.trim().to_string());
        }
    }
    header("x-dregg-credential")
        .map(|c| c.trim().to_string())
        .filter(|c| !c.is_empty())
}

/// Map a [`PublishError`] onto the HTTP response the edge returns.
fn publish_error_response(e: PublishError) -> WebResponse {
    let status = match &e {
        PublishError::CapRefused { .. } => 403,
        PublishError::NotOwner { .. } => 403,
        PublishError::EmptyContent | PublishError::InvalidName(_) => 400,
        PublishError::Storage(_) => 500,
    };
    WebResponse::error(status, e.to_string())
}

/// Lower-hex a 32-byte id.
fn hex32(b: [u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(64);
    for x in &b {
        let _ = write!(s, "{x:02x}");
    }
    s
}
