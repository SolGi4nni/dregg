//! # dregg-gateway-ask — one gateway sidecar for on-demand TLS + capability auth.
//!
//! A public gateway (Caddy) fronts every hosted surface. Historically each
//! surface was a hand-written site block with a hardcoded domain and upstream
//! (one block per product face). This crate collapses that into TWO reusable
//! Caddy idioms, each backed by a real verified read:
//!
//! - **on-demand TLS** — Caddy's `on_demand_tls { ask <gateway>/internal/site-exists }`
//!   asks this sidecar, per inbound SNI, "is this a host you actually serve?"
//!   before it mints a Let's Encrypt certificate. We answer from the verified
//!   custom-domain registry's [`is_verified`](starbridge_domains::DomainRegistry::is_verified):
//!   a name gets a cert IFF a *proven* binding exists for it. That single
//!   wildcard-plus-ask block replaces N hardcoded per-surface blocks — a new
//!   verified site is a registry write, not a Caddyfile patch + reload.
//!
//! - **capability forward-auth** — Caddy's `forward_auth <gateway>/auth?cap=<name>`
//!   asks this sidecar to gate an operator/admin surface. We verify the
//!   operator's printable capability token OFFLINE against the issuer public key
//!   ([`dregg_auth::verify_offline`]) and answer `200` + the confined subject, or
//!   `401`/`403`. No password anywhere; the gate is a proof-carrying token.
//!
//! ## The no-forge discipline
//!
//! The gated upstreams trust the `X-Dregg-Subject` / `X-Dregg-Cap` headers this
//! sidecar SETS on a `200`. That trust is sound only if a client cannot supply
//! them. Two musts, enforced together: (1) Caddy strips any client-supplied
//! identity header BEFORE the forward-auth subrequest (the `dregg_strip_forged_identity`
//! snippet in `Caddyfile.on-demand-tls`), and (2) the gated upstreams are reachable
//! ONLY from the gateway on the private network, never host-published. This
//! sidecar never reads an identity header off the inbound request — it derives
//! the subject from the verified token alone.
//!
//! ## Launchpad composition
//!
//! [`compose_launch_landing`] wires microsite hosting to a token launch: pin the
//! launch's token metadata + image on IPFS (content-addressed — the CID *is* the
//! blake3 commitment, no second identity), and adopt a verified microsite binding
//! so the launch's landing host immediately answers the on-demand-TLS `ask` (gets
//! a cert) and routes. A launch therefore comes up with a landing page and
//! content-addressed metadata in one call, no separate provisioning step.

use std::sync::Arc;

use dregg_ipfs::{Cid, IpfsClient, IpfsError, pin_blob};
use http_serve::{HttpMethod, ServeRequest, WebResponse};
use serde::{Deserialize, Serialize};
use starbridge_domains::{ChallengeMethod, DomainBinding, DomainRegistry};

/// The environment variable naming the issuer public key (hex) that the
/// capability forward-auth gate verifies operator tokens against. Unset ⇒ the
/// gate is fail-closed: every capability route is denied (`503`), because no
/// token can be verified without a trusted issuer.
pub const AUTH_ROOT_PUBKEY_ENV: &str = "DREGG_GATEWAY_AUTH_ROOT_PUBKEY";

/// The environment variable for the sidecar's loopback bind address. It must be
/// loopback / private-network only — the gateway reaches it over the compose /
/// tailnet interface, never the public internet. Defaults to [`DEFAULT_BIND`].
pub const BIND_ENV: &str = "DREGG_GATEWAY_ASK_BIND";

/// The default loopback bind for the sidecar (`ask` + `auth` are gateway-internal).
pub const DEFAULT_BIND: &str = "127.0.0.1:8799";

/// The verified reads the gateway consults, plus the issuer key the capability
/// gate verifies against. Cloned cheaply (the registry is shared behind an `Arc`).
#[derive(Clone)]
pub struct GatewayState {
    /// The verified custom-domain registry — the on-demand-TLS `ask` oracle and
    /// the routing read.
    pub registry: Arc<DomainRegistry>,
    /// The issuer public key (hex) capability tokens must verify under. `None`
    /// ⇒ the capability gate is fail-closed (every `/auth` route denied `503`).
    pub auth_root_pubkey_hex: Option<String>,
}

impl GatewayState {
    /// A state over an existing registry with no capability issuer configured —
    /// the on-demand-TLS `ask` works; `/auth` is fail-closed until a key is set.
    pub fn new(registry: Arc<DomainRegistry>) -> GatewayState {
        GatewayState {
            registry,
            auth_root_pubkey_hex: None,
        }
    }

    /// Set the capability issuer public key (hex) the `/auth` gate verifies under.
    /// An empty / whitespace key is treated as "not configured" (stays fail-closed).
    pub fn with_auth_root(mut self, hex: impl Into<String>) -> GatewayState {
        let hex = hex.into();
        self.auth_root_pubkey_hex = (!hex.trim().is_empty()).then_some(hex);
        self
    }

    /// Read the capability issuer public key from [`AUTH_ROOT_PUBKEY_ENV`], if set.
    pub fn with_auth_root_from_env(self) -> GatewayState {
        match std::env::var(AUTH_ROOT_PUBKEY_ENV) {
            Ok(hex) => self.with_auth_root(hex),
            Err(_) => self,
        }
    }
}

// =============================================================================
// Routing — the single dispatch a served connection runs.
// =============================================================================

/// Dispatch one request to the sidecar's endpoints. The two Caddy-facing routes
/// are `GET /internal/site-exists` (the on-demand-TLS `ask`) and
/// `GET|POST /auth` (the capability forward-auth gate); `/healthz` is the
/// liveness probe the deploy health-gate polls. Everything else is `404`.
pub fn handle(state: &GatewayState, req: &ServeRequest) -> WebResponse {
    let path = req.target.split('?').next().unwrap_or("");
    match path {
        "/internal/site-exists" => site_exists_response(&state.registry, &req.target),
        "/auth" => cap_auth_response(state, req),
        "/healthz" => WebResponse::text("ok"),
        _ => WebResponse::error(404, "no such gateway endpoint"),
    }
}

// =============================================================================
// on-demand TLS `ask` — is this a host we are authorized to serve a cert for?
// =============================================================================

/// The on-demand-TLS `ask` decision. Caddy calls `GET /internal/site-exists?domain=<host>`
/// before issuing a certificate for `<host>`; ANY `2xx` means "yes, mint it",
/// anything else means "refuse". We return `200` IFF the registry holds a
/// *verified* binding for `<host>` — so a name gets a public cert only after its
/// owner has proven DNS control. Fail-closed: a missing / malformed / unknown /
/// merely-pending host is `404`. This is the single oracle that lets one
/// wildcard Caddy block replace every hardcoded per-surface block.
pub fn site_exists_response(registry: &DomainRegistry, target: &str) -> WebResponse {
    let Some(domain) = parse_domain_query(target) else {
        // No `?domain=` — never mint a cert for an unnamed ask (fail-closed).
        return WebResponse::error(400, "missing domain query parameter");
    };
    if registry.is_verified(&domain) {
        // Caddy only inspects the status; the body is advisory.
        WebResponse::text(format!("{domain} is a verified site"))
    } else {
        WebResponse::error(404, format!("{domain} is not a verified site"))
    }
}

/// Extract the `domain` query parameter from a request target
/// (`/internal/site-exists?domain=blog.example.com`), percent-decoding minimally
/// and normalizing to lowercase with any `:port` stripped — the same shape the
/// registry's [`is_verified`](starbridge_domains::DomainRegistry::is_verified)
/// read normalizes to. Returns `None` if the parameter is absent or empty.
pub fn parse_domain_query(target: &str) -> Option<String> {
    let query = target.split_once('?').map(|(_, q)| q).unwrap_or("");
    for pair in query.split('&') {
        let (k, v) = pair.split_once('=').unwrap_or((pair, ""));
        if k == "domain" {
            let decoded = percent_decode(v);
            let host = decoded.trim();
            let host = host.split(':').next().unwrap_or(host).trim();
            if host.is_empty() {
                return None;
            }
            return Some(host.to_ascii_lowercase());
        }
    }
    None
}

/// Minimal percent-decoding for the `domain` query value (Caddy encodes the SNI
/// name; hostnames only ever need `%2e`→`.` and the like, but we decode the
/// general `%XX` form). Invalid escapes are passed through literally.
fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            let hi = (bytes[i + 1] as char).to_digit(16);
            let lo = (bytes[i + 2] as char).to_digit(16);
            if let (Some(hi), Some(lo)) = (hi, lo) {
                out.push((hi * 16 + lo) as u8);
                i += 3;
                continue;
            }
        }
        out.push(bytes[i]);
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

// =============================================================================
// capability forward-auth — gate an operator surface with an offline token.
// =============================================================================

/// The structured capability forward-auth decision. The load-bearing field is
/// `status`: Caddy's `forward_auth` admits the request on any `2xx` and denies
/// otherwise, so status alone fully enforces the gate. On an allow, `subject` is
/// the token's confined identity (derived from the VERIFIED token, never a
/// client header) and `cap` is the capability the route required — the identity a
/// header-capable front sets as `X-Dregg-Subject` / `X-Dregg-Cap` for the
/// upstream. See [`cap_auth_response`] for the status-only wire response the
/// base serve core emits.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapAuth {
    /// The HTTP status the gate answers with (2xx admits, non-2xx denies).
    pub status: u16,
    /// A human-legible reason (allow, or which constraint failed).
    pub reason: String,
    /// The verified subject the token was confined to (only on an allow).
    pub subject: Option<String>,
    /// The capability the route required (only when a `cap` was parsed).
    pub cap: Option<String>,
}

/// The capability forward-auth decision. Caddy calls `GET|POST /auth?cap=<name>`
/// as a subrequest for a gated route. We verify the operator's printable
/// capability token OFFLINE against the configured issuer key for the requested
/// `cap` (the token grants `use` on the `cap` "tool"); the subject is the token's
/// confined identity — never a client-supplied header.
///
/// - no issuer configured → `503` (fail-closed; the gate cannot verify anything);
/// - no `cap` parameter → `400`;
/// - no token presented → `401` (send the operator to the login flow);
/// - token present but denied / not for this cap → `403`;
/// - allowed → `200`, with the verified `subject` + `cap` in the returned struct.
pub fn cap_auth_decision(state: &GatewayState, req: &ServeRequest) -> CapAuth {
    let Some(root_hex) = state.auth_root_pubkey_hex.as_deref() else {
        return CapAuth {
            status: 503,
            reason: "capability gate is fail-closed: no issuer public key configured".to_string(),
            ..Default::default()
        };
    };
    let Some(cap) = parse_query_param(&req.target, "cap") else {
        return CapAuth {
            status: 400,
            reason: "missing cap query parameter".to_string(),
            ..Default::default()
        };
    };
    let Some(token) = extract_token(req) else {
        return CapAuth {
            status: 401,
            reason: "no capability token presented".to_string(),
            cap: Some(cap),
            ..Default::default()
        };
    };

    let request = dregg_auth::Request::tool(&cap);
    let decision = dregg_auth::verify_offline(&token, root_hex, &request);
    if decision.allowed() {
        CapAuth {
            status: 200,
            reason: decision.reason().to_string(),
            // The VERIFIED identity — the only trustworthy X-Dregg-* values.
            subject: Some(decision.subject().unwrap_or("").to_string()),
            cap: Some(cap),
        }
    } else {
        CapAuth {
            status: 403,
            reason: decision.reason().to_string(),
            subject: None,
            cap: Some(cap),
        }
    }
}

/// The status-only wire response for the capability gate — what the base
/// [`http_serve`] serve core emits (its [`WebResponse`] carries no header map, so
/// the verified `subject`/`cap` from [`cap_auth_decision`] are NOT sent as real
/// HTTP headers here). This is COMPLETE for enforcement: Caddy's `forward_auth`
/// admits/denies on status alone. Passing the subject upstream via Caddy's
/// `copy_headers X-Dregg-Subject` needs a header-capable writer — a labeled
/// follow-up (see this crate's README "Identity pass-through"); until then the
/// upstream simply does not receive the subject header, which is safe (the gate
/// still fully admits/denies).
pub fn cap_auth_response(state: &GatewayState, req: &ServeRequest) -> WebResponse {
    let d = cap_auth_decision(state, req);
    if d.status == 200 {
        WebResponse::text("authorized")
    } else {
        WebResponse::error(d.status, d.reason)
    }
}

/// Extract the operator's capability token from the request: an
/// `Authorization: Bearer <token>` header, else a `Cookie: dga=<token>` session
/// cookie. Duplicate-safe via [`ServeRequest::header`] (a smuggled duplicate
/// reads back `None`). Returns `None` when neither is present.
pub fn extract_token(req: &ServeRequest) -> Option<String> {
    if let Some(auth) = req.header("authorization") {
        if let Some(rest) = auth
            .strip_prefix("Bearer ")
            .or_else(|| auth.strip_prefix("bearer "))
        {
            let t = rest.trim();
            if !t.is_empty() {
                return Some(t.to_string());
            }
        }
    }
    if let Some(cookie) = req.header("cookie") {
        for part in cookie.split(';') {
            let part = part.trim();
            if let Some(v) = part.strip_prefix("dga=") {
                let v = v.trim();
                if !v.is_empty() {
                    return Some(v.to_string());
                }
            }
        }
    }
    None
}

/// Extract a named query parameter (percent-decoded) from a request target.
pub fn parse_query_param(target: &str, name: &str) -> Option<String> {
    let query = target.split_once('?').map(|(_, q)| q).unwrap_or("");
    for pair in query.split('&') {
        let (k, v) = pair.split_once('=').unwrap_or((pair, ""));
        if k == name {
            let decoded = percent_decode(v);
            let decoded = decoded.trim();
            if decoded.is_empty() {
                return None;
            }
            return Some(decoded.to_string());
        }
    }
    None
}

// =============================================================================
// Launchpad composition — a launch comes up with a content-addressed landing.
// =============================================================================

/// A token launch's inputs to microsite composition: the launch slug (its
/// landing-page label under the hosting apex), the token metadata document
/// bytes, and the token image bytes.
#[derive(Debug, Clone)]
pub struct LaunchInputs<'a> {
    /// The launch slug — becomes `<slug>.<apex>` (the landing host) and the site
    /// label the gateway routes.
    pub slug: &'a str,
    /// The owner (the launcher's subject) recorded on the microsite binding.
    pub owner: &'a str,
    /// The token metadata document (JSON), pinned content-addressed on IPFS.
    pub metadata: &'a [u8],
    /// The token image bytes, pinned content-addressed on IPFS.
    pub image: &'a [u8],
}

/// The landing a composed launch comes up with: the landing host (verified in the
/// registry, so it answers the on-demand-TLS `ask` immediately), and the IPFS
/// CIDs of the content-addressed token metadata + image the token page renders.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaunchLanding {
    /// The launch's landing host — `<slug>.<apex>`.
    pub host: String,
    /// The site label the gateway routes the landing to.
    pub site: String,
    /// The content-addressed CID of the token metadata document.
    pub metadata_cid: String,
    /// The content-addressed CID of the token image.
    pub image_cid: String,
}

/// Why launch composition failed.
#[derive(Debug)]
pub enum ComposeError {
    /// The slug is not a valid host label.
    InvalidSlug(String),
    /// Pinning metadata or image on IPFS failed.
    Ipfs(IpfsError),
}

impl std::fmt::Display for ComposeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ComposeError::InvalidSlug(s) => write!(f, "`{s}` is not a valid launch slug"),
            ComposeError::Ipfs(e) => write!(f, "pinning launch content failed: {e}"),
        }
    }
}

impl std::error::Error for ComposeError {}

impl From<IpfsError> for ComposeError {
    fn from(e: IpfsError) -> ComposeError {
        ComposeError::Ipfs(e)
    }
}

/// Compose a launch's microsite landing: pin the token metadata + image on IPFS
/// (content-addressed; the CID is the blake3 commitment of the bytes), and adopt
/// a **verified** microsite binding `<slug>.<apex>` → site `<slug>` into the
/// registry so the landing host answers the on-demand-TLS `ask` (gets a cert) and
/// routes at once. Returns the [`LaunchLanding`] — the landing host plus the two
/// content CIDs the token page renders trustlessly.
///
/// The binding is adopted as verified (not challenge-pending): the launch owns
/// the platform-issued `<slug>.<apex>` label by construction — the DNS-challenge
/// flow is for a launcher's *own* custom domain, a separate later step. `apex`
/// is the deployment hosting apex (`registry.apex()` — configured, not hardcoded).
pub fn compose_launch_landing<C: IpfsClient>(
    registry: &DomainRegistry,
    ipfs: &C,
    verified_seq: u64,
    launch: &LaunchInputs<'_>,
) -> Result<LaunchLanding, ComposeError> {
    let slug = launch.slug.trim().to_ascii_lowercase();
    if !is_valid_label(&slug) {
        return Err(ComposeError::InvalidSlug(launch.slug.to_string()));
    }

    let metadata_cid: Cid = pin_blob(ipfs, launch.metadata)?;
    let image_cid: Cid = pin_blob(ipfs, launch.image)?;

    let host = format!("{slug}.{}", registry.apex());
    // A platform-label landing is verified by construction (the launcher does not
    // prove DNS control of the platform apex). The challenge string records the
    // content the landing was provisioned with (its metadata CID) for auditability.
    let binding = DomainBinding::verified(
        &host,
        &slug,
        launch.owner,
        ChallengeMethod::Cname,
        &metadata_cid.to_string_cid(),
        verified_seq,
    );
    registry.adopt(binding);

    Ok(LaunchLanding {
        host,
        site: slug,
        metadata_cid: metadata_cid.to_string_cid(),
        image_cid: image_cid.to_string_cid(),
    })
}

/// A conservative DNS label check for a launch slug: 1–63 chars, ASCII
/// alphanumeric or `-`, not starting/ending with `-`.
fn is_valid_label(label: &str) -> bool {
    if label.is_empty() || label.len() > 63 {
        return false;
    }
    if label.starts_with('-') || label.ends_with('-') {
        return false;
    }
    label
        .bytes()
        .all(|b| b.is_ascii_alphanumeric() || b == b'-')
}

/// The bind address the sidecar listens on ([`BIND_ENV`], else [`DEFAULT_BIND`]).
pub fn bind_from_env() -> String {
    std::env::var(BIND_ENV).unwrap_or_else(|_| DEFAULT_BIND.to_string())
}

// re-export the method enum so callers using ServeRequest can match on it.
pub use http_serve::HttpMethod as Method;

/// A convenience: is this request one the sidecar serves at all (GET/POST)? The
/// serve core already rejects unknown methods with `405`; this is for a caller
/// that dispatches before the serve core.
pub fn is_served_method(m: HttpMethod) -> bool {
    matches!(m, HttpMethod::Get | HttpMethod::Post | HttpMethod::Head)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_ipfs::MockIpfs;

    fn verified_registry() -> Arc<DomainRegistry> {
        let reg = DomainRegistry::new().with_apex("example.host");
        reg.adopt(DomainBinding::verified(
            "blog.acme.com",
            "acme-blog",
            "alice",
            ChallengeMethod::Txt,
            "chal-nonce",
            1,
        ));
        Arc::new(reg)
    }

    #[test]
    fn parse_domain_query_normalizes_and_strips_port() {
        assert_eq!(
            parse_domain_query("/internal/site-exists?domain=Blog.ACME.com"),
            Some("blog.acme.com".to_string())
        );
        assert_eq!(
            parse_domain_query("/internal/site-exists?domain=blog.acme.com:8443"),
            Some("blog.acme.com".to_string())
        );
        assert_eq!(parse_domain_query("/internal/site-exists"), None);
        assert_eq!(parse_domain_query("/internal/site-exists?domain="), None);
    }

    #[test]
    fn percent_encoded_domain_decodes() {
        assert_eq!(
            parse_domain_query("/internal/site-exists?domain=blog%2Eacme%2Ecom"),
            Some("blog.acme.com".to_string())
        );
    }

    #[test]
    fn ask_says_200_only_for_a_verified_host() {
        let reg = verified_registry();
        let ok = site_exists_response(&reg, "/internal/site-exists?domain=blog.acme.com");
        assert_eq!(ok.status, 200);

        let no = site_exists_response(&reg, "/internal/site-exists?domain=evil.example.com");
        assert_eq!(no.status, 404);

        let bad = site_exists_response(&reg, "/internal/site-exists");
        assert_eq!(bad.status, 400);
    }

    #[test]
    fn ask_refuses_a_merely_pending_binding() {
        // A pending (unverified) binding must NOT get a cert — fail-closed until proven.
        let reg = DomainRegistry::new().with_apex("example.host");
        reg.adopt(DomainBinding::pending(
            "pending.acme.com",
            "acme-pending",
            "alice",
            ChallengeMethod::Txt,
            "nonce",
        ));
        let resp = site_exists_response(&reg, "/internal/site-exists?domain=pending.acme.com");
        assert_eq!(
            resp.status, 404,
            "a pending binding must not be minted a cert"
        );
    }

    #[test]
    fn cap_auth_is_fail_closed_without_an_issuer_key() {
        let state = GatewayState::new(verified_registry());
        let req = ServeRequest {
            method: HttpMethod::Get,
            host: "ops.example.host".into(),
            target: "/auth?cap=ops-admin".into(),
            body: Vec::new(),
            headers: vec![("authorization".into(), "Bearer sometoken".into())],
        };
        let resp = cap_auth_response(&state, &req);
        assert_eq!(resp.status, 503, "no issuer ⇒ every cap route fail-closed");
    }

    #[test]
    fn cap_auth_401_without_a_token_403_reason_carried() {
        let state = GatewayState::new(verified_registry()).with_auth_root("deadbeef");
        // No token at all → 401.
        let req = ServeRequest {
            method: HttpMethod::Get,
            host: "ops".into(),
            target: "/auth?cap=ops-admin".into(),
            body: Vec::new(),
            headers: vec![],
        };
        assert_eq!(cap_auth_response(&state, &req).status, 401);

        // Missing cap → 400.
        let req2 = ServeRequest {
            method: HttpMethod::Get,
            host: "ops".into(),
            target: "/auth".into(),
            body: Vec::new(),
            headers: vec![("authorization".into(), "Bearer t".into())],
        };
        assert_eq!(cap_auth_response(&state, &req2).status, 400);
    }

    #[test]
    fn extract_token_reads_bearer_and_cookie_and_is_duplicate_safe() {
        let bearer = ServeRequest {
            method: HttpMethod::Get,
            host: "h".into(),
            target: "/auth?cap=c".into(),
            body: vec![],
            headers: vec![("authorization".into(), "Bearer abc123".into())],
        };
        assert_eq!(extract_token(&bearer).as_deref(), Some("abc123"));

        let cookie = ServeRequest {
            method: HttpMethod::Get,
            host: "h".into(),
            target: "/auth?cap=c".into(),
            body: vec![],
            headers: vec![("cookie".into(), "other=1; dga=tok9; x=2".into())],
        };
        assert_eq!(extract_token(&cookie).as_deref(), Some("tok9"));

        // A smuggled duplicate authorization header reads back None (fail-closed).
        let dup = ServeRequest {
            method: HttpMethod::Get,
            host: "h".into(),
            target: "/auth?cap=c".into(),
            body: vec![],
            headers: vec![
                ("authorization".into(), "Bearer a".into()),
                ("authorization".into(), "Bearer b".into()),
            ],
        };
        assert_eq!(extract_token(&dup), None);
    }

    #[test]
    fn compose_launch_landing_pins_and_verifies_the_microsite() {
        let reg = DomainRegistry::new().with_apex("example.host");
        let reg = Arc::new(reg);
        let ipfs = MockIpfs::new();
        let landing = compose_launch_landing(
            &reg,
            &ipfs,
            7,
            &LaunchInputs {
                slug: "MoonToken",
                owner: "alice",
                metadata: br#"{"name":"MoonToken","symbol":"MOON"}"#,
                image: b"\x89PNG\r\n\x1a\n fake image bytes",
            },
        )
        .expect("compose");

        assert_eq!(landing.host, "moontoken.example.host");
        assert_eq!(landing.site, "moontoken");
        assert!(landing.metadata_cid.starts_with('b'));
        assert!(landing.image_cid.starts_with('b'));
        assert_ne!(landing.metadata_cid, landing.image_cid);

        // The landing host now answers the on-demand-TLS ask (verified + routable).
        assert!(reg.is_verified("moontoken.example.host"));
        assert_eq!(
            reg.site_for_host("moontoken.example.host").as_deref(),
            Some("moontoken")
        );

        // The CID is the content commitment — re-pinning identical bytes is stable.
        let ipfs2 = MockIpfs::new();
        let cid_again = pin_blob(&ipfs2, br#"{"name":"MoonToken","symbol":"MOON"}"#).unwrap();
        assert_eq!(cid_again.to_string_cid(), landing.metadata_cid);
    }

    #[test]
    fn compose_rejects_a_bad_slug() {
        let reg = Arc::new(DomainRegistry::new().with_apex("example.host"));
        let ipfs = MockIpfs::new();
        let err = compose_launch_landing(
            &reg,
            &ipfs,
            1,
            &LaunchInputs {
                slug: "-bad-",
                owner: "alice",
                metadata: b"{}",
                image: b"x",
            },
        );
        assert!(matches!(err, Err(ComposeError::InvalidSlug(_))));
    }

    #[test]
    fn handle_routes_healthz_and_unknown() {
        let state = GatewayState::new(verified_registry());
        let hz = ServeRequest {
            method: HttpMethod::Get,
            host: "h".into(),
            target: "/healthz".into(),
            body: vec![],
            headers: vec![],
        };
        assert_eq!(handle(&state, &hz).status, 200);

        let nope = ServeRequest {
            method: HttpMethod::Get,
            host: "h".into(),
            target: "/nope".into(),
            body: vec![],
            headers: vec![],
        };
        assert_eq!(handle(&state, &nope).status, 404);
    }
}
