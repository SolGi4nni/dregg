//! The cap-gated HTTP **write** path — publish a microsite, run a launch, take a site
//! down — over HTTP, not just as an in-process Rust API.
//!
//! The retired gateway's `/api/*` was GET-only: publishing a microsite and running a
//! launch were in-process Rust calls with no route, so a real console could not *do*
//! anything over the wire. This handler exposes the hosting primitives as `POST` / `PUT`
//! / `DELETE`, each gated by the SAME verify-don't-trust subject the reads use — the
//! **owner is the verified subject**, never a value the client asserts in the body.
//!
//! ```text
//!   POST   /api/sites                publish (or owner-republish) a microsite
//!   DELETE /api/sites/{name}         take a microsite down (owner-only)
//!   POST   /api/launches            compose + publish a launch's landing microsite
//! ```
//!
//! ## Idempotency
//!
//! A mutating request may carry an `Idempotency-Key` header. The first request under a
//! `(subject, key)` pair executes and its response is cached; a retry with the same key
//! replays the cached response without re-executing — so a client that retries a create
//! after a dropped connection does not double-publish. The cache is bounded
//! ([`IDEMPOTENCY_CAP`]) and in-memory (a per-process best-effort, documented as such).

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use http_serve::{HttpMethod, WebResponse};
use serde::Deserialize;

use crate::launchpad::{Launch, compose_unpinned};
use crate::microsite::{Asset, Microsite, SiteError, SiteRegistry};
use crate::util::lock;

/// The path prefix the write surfaces share with the reads.
const API_PREFIX: &str = "/api";
/// The largest number of cached idempotency responses kept in memory.
pub const IDEMPOTENCY_CAP: usize = 4096;

/// One asset in a publish request. `text` (a UTF-8 body) is the common case; `bytes`
/// (a raw byte array) covers binary assets. `content_type` defaults to the type
/// inferred from `path`'s extension.
#[derive(Debug, Clone, Deserialize)]
pub struct AssetSpec {
    /// The request path the asset serves at (e.g. `/index.html`).
    pub path: String,
    /// An explicit content-type; inferred from the path extension when absent.
    #[serde(default)]
    pub content_type: Option<String>,
    /// A UTF-8 body.
    #[serde(default)]
    pub text: Option<String>,
    /// A raw byte body (for binary assets).
    #[serde(default)]
    pub bytes: Option<Vec<u8>>,
}

/// A publish-microsite request (`POST /api/sites`).
#[derive(Debug, Clone, Deserialize)]
pub struct PublishSiteRequest {
    /// The site `<name>` (its `<name>.<apex>` host serves the bytes).
    pub name: String,
    /// The assets to publish.
    #[serde(default)]
    pub assets: Vec<AssetSpec>,
}

/// A run-launch request (`POST /api/launches`). Mirrors [`Launch`], minus the owner
/// (which is the verified subject, never client-asserted).
#[derive(Debug, Clone, Deserialize, Default)]
pub struct LaunchRequest {
    /// The slug — the site `<name>` and `<slug>.<apex>` host.
    pub slug: String,
    /// The landing title.
    #[serde(default)]
    pub title: String,
    /// The landing blurb.
    #[serde(default)]
    pub blurb: String,
    /// Optional content-addressed launch metadata (published as `metadata.json`).
    #[serde(default)]
    pub metadata: Option<serde_json::Value>,
    /// Optional caller-supplied landing `index.html`, overriding the template.
    #[serde(default)]
    pub landing_html: Option<String>,
    /// Optional content-addressed image `(filename, bytes)`.
    #[serde(default)]
    pub image: Option<(String, Vec<u8>)>,
}

/// The cap-gated write handler. Holds the shared [`SiteRegistry`] the reads also serve,
/// plus a bounded idempotency cache.
pub struct WriteHandler {
    sites: Arc<SiteRegistry>,
    idempotency: Mutex<BTreeMap<String, (u16, Vec<u8>)>>,
}

impl WriteHandler {
    /// A write handler over the shared `sites` registry.
    pub fn new(sites: Arc<SiteRegistry>) -> WriteHandler {
        WriteHandler {
            sites,
            idempotency: Mutex::new(BTreeMap::new()),
        }
    }

    /// Whether this handler serves `(method, path)`: a mutating verb on a write surface.
    pub fn serves(method: HttpMethod, path: &str) -> bool {
        let p = path.split('?').next().unwrap_or(path);
        matches!(
            (method, p),
            (HttpMethod::Post, "/api/sites") | (HttpMethod::Post, "/api/launches")
        ) || (method == HttpMethod::Delete && p.starts_with("/api/sites/"))
            || (method == HttpMethod::Put && p.starts_with("/api/sites/"))
    }

    /// Route + serve one write. `subject` is the verified owner (a `None` fails closed
    /// `401`); `idem_key` is the optional `Idempotency-Key` header value.
    pub fn respond(
        &self,
        method: HttpMethod,
        target: &str,
        body: &[u8],
        subject: Option<&str>,
        idem_key: Option<&str>,
    ) -> WebResponse {
        let Some(subject) = subject.map(str::trim).filter(|s| !s.is_empty()) else {
            return WebResponse::error(
                401,
                "the write surfaces are cap-gated; present a verified subject",
            );
        };
        let path = target.split('?').next().unwrap_or(target);

        // Idempotency replay: a repeated (subject, key) returns the cached response.
        let cache_key = idem_key
            .map(str::trim)
            .filter(|k| !k.is_empty())
            .map(|k| format!("{subject}\u{0}{k}"));
        if let Some(key) = &cache_key {
            if let Some((status, body)) = lock(&self.idempotency).get(key).cloned() {
                return WebResponse {
                    status,
                    content_type: "application/json".to_string(),
                    body,
                };
            }
        }

        let resp = match (method, path) {
            (HttpMethod::Post, "/api/sites") => self.publish_site(subject, body),
            (HttpMethod::Post, "/api/launches") => self.run_launch(subject, body),
            (HttpMethod::Delete, p) | (HttpMethod::Put, p) if p.starts_with("/api/sites/") => {
                let name = &p["/api/sites/".len()..];
                if method == HttpMethod::Delete {
                    self.take_down(subject, name)
                } else {
                    // PUT /api/sites/{name} = publish, name taken from the path.
                    self.publish_named(subject, name, body)
                }
            }
            _ => WebResponse::error(404, "unknown write surface"),
        };

        // Cache a successful (2xx) response under its idempotency key.
        if let Some(key) = cache_key {
            if (200..300).contains(&resp.status) {
                let mut cache = lock(&self.idempotency);
                if cache.len() >= IDEMPOTENCY_CAP {
                    // Bounded: drop the lexicographically-first entry (crude but capped).
                    if let Some(first) = cache.keys().next().cloned() {
                        cache.remove(&first);
                    }
                }
                cache.insert(key, (resp.status, resp.body.clone()));
            }
        }
        resp
    }

    fn publish_site(&self, subject: &str, body: &[u8]) -> WebResponse {
        let req: PublishSiteRequest = match serde_json::from_slice(body) {
            Ok(r) => r,
            Err(e) => return WebResponse::error(400, format!("bad publish body: {e}")),
        };
        self.do_publish(subject, &req.name, &req.assets)
    }

    fn publish_named(&self, subject: &str, name: &str, body: &[u8]) -> WebResponse {
        let assets: Vec<AssetSpec> = match serde_json::from_slice::<PublishSiteRequest>(body) {
            Ok(r) => r.assets,
            Err(_) => match serde_json::from_slice::<Vec<AssetSpec>>(body) {
                Ok(a) => a,
                Err(e) => return WebResponse::error(400, format!("bad publish body: {e}")),
            },
        };
        self.do_publish(subject, name, &assets)
    }

    fn do_publish(&self, subject: &str, name: &str, assets: &[AssetSpec]) -> WebResponse {
        // The owner is the VERIFIED subject — never a client-asserted value.
        let mut site = Microsite::new(name, subject);
        for spec in assets {
            let bytes = match (&spec.text, &spec.bytes) {
                (Some(text), _) => text.clone().into_bytes(),
                (None, Some(bytes)) => bytes.clone(),
                (None, None) => Vec::new(),
            };
            let asset = match &spec.content_type {
                Some(ct) => Asset::new(ct.clone(), bytes),
                None => Asset::at(&spec.path, bytes),
            };
            site = site.with_asset(&spec.path, asset);
        }
        match self.sites.publish(site) {
            Ok(root) => {
                let published = self.sites.get(name);
                let (assets, bytes) = published
                    .as_ref()
                    .map(|s| (s.asset_count(), s.bytes()))
                    .unwrap_or((0, 0));
                let host = format!("{}.{}", name.trim().to_ascii_lowercase(), self.sites.apex());
                json_created(serde_json::json!({
                    "name": name.trim().to_ascii_lowercase(),
                    "owner": subject,
                    "host": host,
                    "content_root": root.to_string_cid(),
                    "assets": assets,
                    "bytes": bytes,
                    "status": "published",
                }))
            }
            Err(e) => site_error_response(e),
        }
    }

    fn run_launch(&self, subject: &str, body: &[u8]) -> WebResponse {
        let req: LaunchRequest = match serde_json::from_slice(body) {
            Ok(r) => r,
            Err(e) => return WebResponse::error(400, format!("bad launch body: {e}")),
        };
        let mut launch =
            Launch::new(subject, req.slug.as_str()).titled(req.title.as_str(), req.blurb.as_str());
        if let Some(meta) = req.metadata {
            launch = launch.with_metadata(meta);
        }
        if let Some(html) = req.landing_html {
            launch = launch.with_landing(html);
        }
        if let Some((filename, bytes)) = req.image {
            launch = launch.with_image(filename, bytes);
        }
        let (site, receipt) = compose_unpinned(&launch, self.sites.apex());
        match self.sites.publish(site) {
            Ok(_) => json_created(serde_json::json!({
                "slug": receipt.slug,
                "owner": receipt.owner,
                "landing_host": receipt.landing_host,
                "site_root": receipt.site_root.to_string_cid(),
                "metadata_cid": receipt.metadata_cid.as_ref().map(|c| c.to_string_cid()),
                "image_cid": receipt.image_cid.as_ref().map(|c| c.to_string_cid()),
            })),
            Err(e) => site_error_response(e),
        }
    }

    fn take_down(&self, subject: &str, name: &str) -> WebResponse {
        if self.sites.take_down(name, subject) {
            json_created(
                serde_json::json!({ "name": name.trim().to_ascii_lowercase(), "status": "taken_down" }),
            )
        } else {
            // No such site OR not the caller's — a 404 either way (existence is not an
            // oracle to a non-owner).
            WebResponse::error(404, "no such site")
        }
    }

    /// Whether the write surfaces reference `path` at all (for routing help).
    pub fn under_api(path: &str) -> bool {
        let p = path.split('?').next().unwrap_or(path);
        p == API_PREFIX || p.starts_with("/api/")
    }
}

fn json_created(value: serde_json::Value) -> WebResponse {
    WebResponse {
        status: 201,
        content_type: "application/json".to_string(),
        body: value.to_string().into_bytes(),
    }
}

fn site_error_response(e: SiteError) -> WebResponse {
    let status = match e {
        SiteError::InvalidName(_) => 400,
        SiteError::OwnerMismatch { .. } => 403,
        SiteError::TooLarge { .. } => 413,
        SiteError::NoOwner => 401,
    };
    WebResponse::error(status, e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE: &str = "dregg:alice";
    const BOB: &str = "dregg:bob";

    fn handler() -> WriteHandler {
        WriteHandler::new(Arc::new(SiteRegistry::new("dregg.net")))
    }

    fn publish_body() -> Vec<u8> {
        serde_json::to_vec(&serde_json::json!({
            "name": "blog",
            "assets": [
                { "path": "/index.html", "text": "<h1>hi</h1>" },
                { "path": "/style.css", "text": "h1{color:teal}" }
            ]
        }))
        .unwrap()
    }

    #[test]
    fn publish_over_http_owner_is_the_subject_and_site_goes_live() {
        let h = handler();
        let resp = h.respond(
            HttpMethod::Post,
            "/api/sites",
            &publish_body(),
            Some(ALICE),
            None,
        );
        assert_eq!(resp.status, 201, "{}", resp.body_str());
        let v: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
        assert_eq!(v["owner"], ALICE);
        assert_eq!(v["assets"], 2);
        assert_eq!(v["host"], "blog.dregg.net");
        // The site is live in the shared registry.
        assert_eq!(h.sites.get("blog").unwrap().owner, ALICE);
    }

    #[test]
    fn a_stranger_cannot_republish_anothers_site() {
        let h = handler();
        h.respond(
            HttpMethod::Post,
            "/api/sites",
            &publish_body(),
            Some(ALICE),
            None,
        );
        let bob = h.respond(
            HttpMethod::Post,
            "/api/sites",
            &publish_body(),
            Some(BOB),
            None,
        );
        assert_eq!(bob.status, 403, "no takeover: {}", bob.body_str());
    }

    #[test]
    fn write_requires_a_subject() {
        let h = handler();
        assert_eq!(
            h.respond(HttpMethod::Post, "/api/sites", &publish_body(), None, None)
                .status,
            401
        );
    }

    #[test]
    fn idempotency_key_replays_not_re_executes() {
        let h = handler();
        let first = h.respond(
            HttpMethod::Post,
            "/api/sites",
            &publish_body(),
            Some(ALICE),
            Some("key-1"),
        );
        assert_eq!(first.status, 201);
        // A second publish under the same key returns the cached response — even though
        // the body here is different, the key wins (that is the idempotency contract).
        let other_body = serde_json::to_vec(&serde_json::json!({
            "name": "blog", "assets": [{ "path": "/index.html", "text": "CHANGED" }]
        }))
        .unwrap();
        let replay = h.respond(
            HttpMethod::Post,
            "/api/sites",
            &other_body,
            Some(ALICE),
            Some("key-1"),
        );
        assert_eq!(replay.body, first.body, "the cached response is replayed");
        // The site was NOT overwritten by the replayed request.
        assert_eq!(
            h.sites.get("blog").unwrap().serve("/index.html").body,
            b"<h1>hi</h1>"
        );
    }

    #[test]
    fn run_a_launch_over_http() {
        let h = handler();
        let body = serde_json::to_vec(&serde_json::json!({
            "slug": "moon",
            "title": "Moon",
            "blurb": "to the moon",
            "metadata": { "symbol": "MOON" }
        }))
        .unwrap();
        let resp = h.respond(HttpMethod::Post, "/api/launches", &body, Some(ALICE), None);
        assert_eq!(resp.status, 201, "{}", resp.body_str());
        let v: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
        assert_eq!(v["landing_host"], "moon.dregg.net");
        assert!(v["metadata_cid"].as_str().unwrap().starts_with('b'));
        // Live landing page.
        let landing = h.sites.get("moon").unwrap().serve("/");
        assert_eq!(landing.status, 200);
        assert!(String::from_utf8_lossy(&landing.body).contains("Moon"));
    }

    #[test]
    fn take_down_is_owner_enforced() {
        let h = handler();
        h.respond(
            HttpMethod::Post,
            "/api/sites",
            &publish_body(),
            Some(ALICE),
            None,
        );
        // A stranger cannot take it down (404, existence not confirmed).
        assert_eq!(
            h.respond(HttpMethod::Delete, "/api/sites/blog", &[], Some(BOB), None)
                .status,
            404
        );
        assert!(h.sites.get("blog").is_some(), "still up");
        // The owner can.
        assert_eq!(
            h.respond(
                HttpMethod::Delete,
                "/api/sites/blog",
                &[],
                Some(ALICE),
                None
            )
            .status,
            201
        );
        assert!(h.sites.get("blog").is_none(), "taken down");
    }

    #[test]
    fn serves_predicate() {
        assert!(WriteHandler::serves(HttpMethod::Post, "/api/sites"));
        assert!(WriteHandler::serves(HttpMethod::Post, "/api/launches"));
        assert!(WriteHandler::serves(HttpMethod::Delete, "/api/sites/blog"));
        assert!(!WriteHandler::serves(HttpMethod::Get, "/api/sites"));
        assert!(!WriteHandler::serves(HttpMethod::Post, "/api/machines"));
    }
}
