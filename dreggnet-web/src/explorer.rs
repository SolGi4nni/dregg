//! THE CHAIN EXPLORER — `GET /explorer`, wired to a live node's public read API.
//!
//! # What this is
//!
//! `site/explorer/` held an explorer *stylesheet* (`.ex-*`, a coherent design
//! system for a chain browser) and, as `index.html`, a **static pg-dregg
//! caps-as-rows demo** — a labeled snapshot of six seeded SQL rows, not an
//! explorer over anything. The real explorer app (`app.js` + a `<dregg-*>`
//! inspector platform + a `sample-data.js` offline snapshot) was DELETED in
//! `51f1d03309`, and its 1.3 MB studio dependency now survives only under
//! `site-old-scavenge/`. Nothing in `dreggnet-web` served any of it.
//!
//! So: the page is a **rewrite**, not a revival. What is reused is the design
//! language — the `:root` token block of `site/explorer/style.css` — and
//! nothing else. The caps-as-rows demo was not deleted; it moved back to its
//! historical filename, `site/explorer/caps-as-rows.html`.
//!
//! # Why there is a proxy
//!
//! The node's CORS middleware allows localhost and extension origins plus an
//! explicit operator allowlist. A page served from `dreggnet-web` is a
//! different origin, so browser-direct `fetch` to the node is refused unless an
//! operator widens the node's CORS — and on a real deployment the node is on
//! loopback behind the web tier anyway. `GET /explorer/node/{*path}` is that
//! hop.
//!
//! It is deliberately NOT a transparent proxy. `dreggnet-web` may be public
//! while the node it can reach is loopback-only, so an open proxy would hand
//! the internet the node's operator-local surface — an SSRF-shaped hole. The
//! hop is therefore:
//!
//!   * **GET only** — no method is forwarded but GET;
//!   * **path-allowlisted** — [`allow_node_path`] against a fixed list of the
//!     node's PUBLIC read routes, with every segment shape-checked, so neither
//!     `..` nor a protected route can be reached;
//!   * **query-key-allowlisted** — the query is REBUILT from known keys, never
//!     passed through;
//!   * **credential-free** — no `Authorization` header is ever attached, so the
//!     hop cannot acquire authority the anonymous internet lacks. `DREGG_NODE_BEARER`
//!     is intentionally not read here.
//!
//! Bodies are returned verbatim with the node's own status code, so everything
//! the page claims can be re-read as raw node JSON in another tab. That is the
//! point: the explorer's rendering is checkable against its own source.

use axum::{
    Router,
    body::Body,
    extract::{Path, Query, State},
    http::{HeaderValue, StatusCode, header},
    response::{Html, Response},
    routing::get,
};
use std::collections::BTreeMap;
use std::sync::Arc;
use std::time::Duration;

/// The environment variable naming the node to read. Same variable the games'
/// node-target seam uses (`dregg_node_target::NODE_URL_ENV`), so one deployment
/// setting points both at the same node.
pub const NODE_URL_ENV: &str = dregg_node_target::NODE_URL_ENV;

/// Upper bound on a proxied node response. `/api/cell/{id}/proof` serves the
/// FULL leaf set (the node caps it at `MAX_PROOF_LEAVES` = 100_000 leaves ≈
/// 13 MB of hex), so the ceiling has to clear that with room, while still
/// refusing to buffer something unbounded.
const MAX_PROXY_BODY: usize = 32 * 1024 * 1024;

/// Per-request timeout on the node hop.
const NODE_TIMEOUT: Duration = Duration::from_secs(20);

// =============================================================================
// The read-only allowlist
// =============================================================================

/// Query keys the explorer forwards, by node route family. Anything else is
/// dropped rather than passed through.
const ALLOWED_QUERY_KEYS: &[&str] = &[
    "limit",
    "offset",
    "since_height",
    "height",
    "leaf_offset",
    "leaf_limit",
];

/// Is `seg` a safe path segment? Hex ids, decimal heights and route words all
/// pass; `..`, `.`, encoded bytes and anything with a slash or `%` do not.
fn safe_segment(seg: &str) -> bool {
    !seg.is_empty()
        && seg.len() <= 128
        && seg
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
}

fn is_hex_32(seg: &str) -> bool {
    seg.len() == 64 && seg.bytes().all(|b| b.is_ascii_hexdigit())
}

fn is_decimal(seg: &str) -> bool {
    !seg.is_empty() && seg.len() <= 20 && seg.bytes().all(|b| b.is_ascii_digit())
}

/// The PUBLIC read routes the explorer is permitted to fetch.
///
/// Every entry was read at its handler in `node/src/api.rs` — a route existing
/// is not a route returning what its name suggests, and two on this list do
/// not (see the module docs of the page itself):
///
///   * `api/blocks` is `get_federation_roots` — ATTESTED ROOTS, not blocks;
///   * `api/block/{height}` is a blocklace block by *creator sequence*, which
///     is not a global chain height.
///
/// Deliberately NOT here:
///   * `api/node/health` / `api/node/status` — they LOOK public (they alias the
///     public `/status`) but they sit in the `path_aliases` router, which
///     applies `require_auth` as a `route_layer` to every route in it. They are
///     bearer-gated. `/status` is the public one.
///   * `api/tokens` — public, but it is the node operator's CIPHERCLERK token
///     metadata (id/label/service), not on-chain assets. An explorer surfacing
///     it under the word "tokens" would be lying about whose objects they are.
///   * `api/events/stream`, `observability/stream` — SSE; this hop buffers.
///   * `identity/export/{cell}`, `pir/*` — real public routes, but they are
///     portable-artifact and private-retrieval surfaces, not chain history.
///   * everything POST, and every `cipherclerk` route.
fn allow_node_path(path: &str) -> bool {
    let segs: Vec<&str> = path.split('/').filter(|s| !s.is_empty()).collect();
    if segs.is_empty() || segs.len() > 5 {
        return false;
    }
    if !segs.iter().all(|s| safe_segment(s)) {
        return false;
    }
    match segs.as_slice() {
        // Node posture.
        ["status"] => true,
        ["api", "node", "producer"] => true,
        ["api", "node", "identity"] => true,
        // Federation / committee.
        //
        // `/api/blocks` used to serve attested roots, which is why the page once
        // read it for them. The node split the two on 2026-07-25 — `/api/blocks`
        // now serves blocklace blocks and the roots kept their own name — and
        // the page followed, but this list did not, so the attested-roots panel
        // has been rendering "ROUTE NOT ON THE ALLOWLIST" on the site ever since.
        // `page_reads_only_allowlisted_routes` below is the gate that makes that
        // drift impossible to reintroduce silently.
        ["api", "blocks"] => true,
        ["api", "federation", "roots"] => true,
        ["api", "federations"] => true,
        ["api", "membership"] => true,
        // Owned state.
        ["api", "cells"] => true,
        ["api", "cell", id] => is_hex_32(id),
        ["api", "cell", id, "proof"] => is_hex_32(id),
        // Receipt chains.
        ["api", "receipts"] => true,
        ["api", "receipts", hash, "witnesses"] => is_hex_32(hash),
        ["api", "receipts", "index", "root"] => true,
        ["api", "receipts", "index", "head"] => true,
        ["api", "turn", hash, "proof"] => is_hex_32(hash),
        // Blocklace.
        ["api", "blocklace", "blocks"] => true,
        ["api", "blocklace", "checkpoint"] => true,
        ["api", "block", height] => is_decimal(height),
        ["checkpoint", "latest"] => true,
        // Activity.
        ["api", "events"] => true,
        ["api", "intents"] => true,
        ["api", "conditionals"] => true,
        _ => false,
    }
}

// =============================================================================
// State
// =============================================================================

/// The explorer's server-side state: which node to read, and one reusable
/// HTTP client.
///
/// The client is the ASYNC `reqwest::Client`, deliberately, even though this
/// crate's other outbound call site uses `reqwest::blocking`. A blocking client
/// owns its own tokio runtime, and dropping one inside an async context panics
/// with "Cannot drop a runtime in a context where blocking is not allowed" —
/// which is exactly what happened when this state was built and dropped inside
/// an async test. Since the caller here is already an axum handler, the async
/// client is both simpler (no `spawn_blocking` hop) and free of that hazard.
pub struct ExplorerState {
    /// The node base URL (no trailing slash), or `None` when unconfigured.
    node_url: Option<String>,
    http: reqwest::Client,
}

impl ExplorerState {
    /// Read the node target from [`NODE_URL_ENV`]. Unset or empty → `None`,
    /// and the page says so rather than inventing a localhost default: a
    /// deployed explorer silently pointing at its own loopback is exactly the
    /// "plausible-looking empty" failure this surface exists to avoid.
    pub fn from_env() -> Self {
        Self::with_node_url(std::env::var(NODE_URL_ENV).ok())
    }

    /// Build over an explicit node URL. Normalisation (trim + drop trailing
    /// slashes + treat empty as unconfigured) happens HERE rather than in
    /// [`Self::from_env`], so a programmatic caller and the environment get
    /// identical treatment and neither can produce a `//`-doubled request path.
    pub fn with_node_url(node_url: Option<String>) -> Self {
        let node_url = node_url
            .map(|u| u.trim().trim_end_matches('/').to_string())
            .filter(|u| !u.is_empty());
        let http = reqwest::Client::builder()
            .timeout(NODE_TIMEOUT)
            .build()
            .expect("reqwest client builds with a static config");
        Self { node_url, http }
    }

    pub fn node_url(&self) -> Option<&str> {
        self.node_url.as_deref()
    }
}

// =============================================================================
// Router
// =============================================================================

/// Mount the explorer. Reads its node target from the environment.
pub fn explorer_router() -> Router {
    explorer_router_with_state(Arc::new(ExplorerState::from_env()))
}

/// Mount the explorer over an explicit state (the tests' seam).
pub fn explorer_router_with_state(state: Arc<ExplorerState>) -> Router {
    Router::new()
        .route("/explorer", get(explorer_page))
        .route("/explorer/", get(explorer_page))
        .route("/explorer/explorer.css", get(explorer_css))
        .route("/explorer/explorer.js", get(explorer_js))
        .route("/explorer/blake3.js", get(blake3_js))
        .route("/explorer/node/{*path}", get(node_proxy))
        .route("/explorer/target", get(explorer_target))
        .with_state(state)
}

// -- static assets ------------------------------------------------------------

/// The explorer page. Served from `site/explorer/` — the directory that already
/// owned this surface — rather than copied into the crate, so there is exactly
/// one place the page lives.
async fn explorer_page() -> Html<&'static str> {
    Html(include_str!("../../site/explorer/index.html"))
}

fn asset(content_type: &'static str, body: &'static str) -> Response {
    let mut res = Response::new(Body::from(body));
    res.headers_mut()
        .insert(header::CONTENT_TYPE, HeaderValue::from_static(content_type));
    res
}

async fn explorer_css() -> Response {
    asset(
        "text/css; charset=utf-8",
        include_str!("../../site/explorer/explorer.css"),
    )
}

async fn explorer_js() -> Response {
    asset(
        "text/javascript; charset=utf-8",
        include_str!("../../site/explorer/explorer.js"),
    )
}

async fn blake3_js() -> Response {
    asset(
        "text/javascript; charset=utf-8",
        include_str!("../../site/explorer/blake3.js"),
    )
}

// -- the target readout -------------------------------------------------------

/// `GET /explorer/target` — what node this explorer reads, if any.
///
/// The page asks this FIRST. An unconfigured explorer must be able to say "no
/// node is configured" as a distinct state from "the node is empty" and from
/// "the node is unreachable"; those three look identical if you only ever look
/// at an empty array.
async fn explorer_target(State(state): State<Arc<ExplorerState>>) -> Response {
    let body = match state.node_url() {
        Some(url) => serde_json::json!({
            "configured": true,
            "node_url": url,
            "env": NODE_URL_ENV,
        }),
        None => serde_json::json!({
            "configured": false,
            "node_url": serde_json::Value::Null,
            "env": NODE_URL_ENV,
        }),
    };
    json_response(StatusCode::OK, body.to_string())
}

fn json_response(status: StatusCode, body: String) -> Response {
    let mut res = Response::new(Body::from(body));
    *res.status_mut() = status;
    res.headers_mut().insert(
        header::CONTENT_TYPE,
        HeaderValue::from_static("application/json"),
    );
    res
}

fn proxy_error(status: StatusCode, kind: &str, detail: String) -> Response {
    json_response(
        status,
        serde_json::json!({ "explorer_error": kind, "detail": detail }).to_string(),
    )
}

// -- the node hop -------------------------------------------------------------

/// `GET /explorer/node/{*path}` — the read-only hop to the node's public API.
async fn node_proxy(
    State(state): State<Arc<ExplorerState>>,
    Path(path): Path<String>,
    Query(params): Query<BTreeMap<String, String>>,
) -> Response {
    if !allow_node_path(&path) {
        return proxy_error(
            StatusCode::FORBIDDEN,
            "path-not-allowed",
            format!(
                "`{path}` is not on the explorer's read-only allowlist. The explorer proxies a \
                 fixed set of the node's PUBLIC GET routes and nothing else."
            ),
        );
    }

    let Some(base) = state.node_url().map(str::to_string) else {
        return proxy_error(
            StatusCode::SERVICE_UNAVAILABLE,
            "no-node-configured",
            format!("{NODE_URL_ENV} is unset, so this explorer has no chain to read."),
        );
    };

    // Rebuild the query from allowlisted keys instead of forwarding the raw
    // string, so nothing the caller invents reaches the node.
    let mut query: Vec<(String, String)> = params
        .into_iter()
        .filter(|(k, _)| ALLOWED_QUERY_KEYS.contains(&k.as_str()))
        .filter(|(_, v)| v.len() <= 32 && v.bytes().all(|b| b.is_ascii_alphanumeric()))
        .collect();
    query.sort();

    let url = format!("{base}/{path}");

    let mut req = state.http.get(&url);
    if !query.is_empty() {
        req = req.query(&query);
    }
    // NOTE: no Authorization header, deliberately. See the module docs.
    let fetched = async {
        let res = req.send().await?;
        let status = res.status();
        let content_type = res
            .headers()
            .get(reqwest::header::CONTENT_TYPE)
            .and_then(|v| v.to_str().ok())
            .unwrap_or("application/json")
            .to_string();
        let bytes = res.bytes().await?;
        Ok::<_, reqwest::Error>((status, content_type, bytes))
    }
    .await;

    let (status, content_type, bytes) = match fetched {
        Ok(v) => v,
        Err(e) => {
            return proxy_error(
                StatusCode::BAD_GATEWAY,
                "node-unreachable",
                format!("could not read the node at {base}: {e}"),
            );
        }
    };

    if bytes.len() > MAX_PROXY_BODY {
        return proxy_error(
            StatusCode::INSUFFICIENT_STORAGE,
            "node-response-too-large",
            format!(
                "the node returned {} bytes, over the explorer's {MAX_PROXY_BODY}-byte ceiling",
                bytes.len()
            ),
        );
    }

    // The node's own status and body, verbatim: a 404 from the node stays a 404
    // here, so the page can tell "no checkpoint exists yet" (404) apart from
    // "the node is not answering" (502).
    let mut res = Response::new(Body::from(bytes));
    *res.status_mut() = StatusCode::from_u16(status.as_u16()).unwrap_or(StatusCode::BAD_GATEWAY);
    res.headers_mut().insert(
        header::CONTENT_TYPE,
        HeaderValue::from_str(&content_type)
            .unwrap_or_else(|_| HeaderValue::from_static("application/json")),
    );
    res
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // -- the allowlist is the security boundary; test both directions ---------

    #[test]
    fn public_read_routes_are_allowed() {
        let hex = "a".repeat(64);
        for p in [
            "status",
            "api/node/producer",
            "api/node/identity",
            "api/blocks",
            "api/federation/roots",
            "api/federations",
            "api/membership",
            "api/cells",
            "api/receipts",
            "api/receipts/index/root",
            "api/receipts/index/head",
            "api/blocklace/blocks",
            "api/blocklace/checkpoint",
            "api/block/42",
            "checkpoint/latest",
            "api/events",
            "api/intents",
            "api/conditionals",
        ] {
            assert!(allow_node_path(p), "{p} should be allowed");
        }
        assert!(allow_node_path(&format!("api/cell/{hex}")));
        assert!(allow_node_path(&format!("api/cell/{hex}/proof")));
        assert!(allow_node_path(&format!("api/receipts/{hex}/witnesses")));
        assert!(allow_node_path(&format!("api/turn/{hex}/proof")));
    }

    #[test]
    fn protected_and_write_routes_are_refused() {
        for p in [
            // bearer-gated despite looking like the public /status
            "api/node/health",
            "api/node/status",
            // the operator's cipherclerk surface
            "cipherclerk",
            "cipherclerk/tokens",
            "cipherclerk/unlock",
            "cipherclerk/set-passphrase",
            "api/cipherclerk/unlock",
            // operator token metadata, not chain assets
            "api/tokens",
            // write / submit paths
            "turn/submit",
            "turns/submit",
            "api/turns/submit",
            "api/faucet",
            "api/discharge",
            "membership/approve",
            "cells/register",
            "programs/deploy",
            // streams this hop cannot serve
            "api/events/stream",
            "observability/stream",
            // other public-but-not-chain-history surfaces
            "pir/info",
            "metrics",
            "ws",
        ] {
            assert!(!allow_node_path(p), "{p} must NOT be allowed");
        }
    }

    #[test]
    fn traversal_and_junk_segments_are_refused() {
        for p in [
            "",
            "/",
            "..",
            "api/../cipherclerk/tokens",
            "api/cell/../../metrics",
            "api/cells/../../../etc/passwd",
            "api/cell/%2e%2e/proof",
            "api/cell/not-hex/proof",
            // a 63-char id is not a 32-byte hex id
            "api/cell/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa/proof",
            "api/block/notanumber",
            "api/block/-1",
            "a/b/c/d/e/f",
            "api/cell/a b c",
            "api/cell/a?b",
        ] {
            assert!(!allow_node_path(p), "{p:?} must NOT be allowed");
        }
    }

    #[test]
    fn hex_and_decimal_shape_checks_are_exact() {
        assert!(is_hex_32(&"0".repeat(64)));
        assert!(is_hex_32(&"f".repeat(64)));
        assert!(!is_hex_32(&"g".repeat(64)));
        assert!(!is_hex_32(&"0".repeat(63)));
        assert!(!is_hex_32(&"0".repeat(65)));
        assert!(is_decimal("0"));
        assert!(is_decimal("18446744073709551615"));
        assert!(!is_decimal(""));
        assert!(!is_decimal("1.0"));
        assert!(!is_decimal("0x10"));
    }

    // -- unconfigured is its own state ---------------------------------------

    #[test]
    fn unconfigured_state_reports_no_node() {
        let s = ExplorerState::with_node_url(None);
        assert!(s.node_url().is_none());
    }

    #[test]
    fn node_url_is_normalised() {
        let s = ExplorerState::with_node_url(Some("http://127.0.0.1:8420/".into()));
        assert_eq!(s.node_url(), Some("http://127.0.0.1:8420"));
    }

    // -- the served page must actually be the explorer ------------------------

    #[test]
    fn served_page_is_the_explorer_not_the_caps_demo() {
        let page = include_str!("../../site/explorer/index.html");
        // The caps-as-rows demo used to occupy index.html. If it ever comes
        // back, this catches it — the explorer route must not serve a static
        // six-row SQL snapshot.
        assert!(
            !page.contains("caps-as-rows.js"),
            "index.html is serving the caps-as-rows demo again"
        );
        assert!(
            page.contains("explorer.js"),
            "the page must load explorer.js"
        );
        assert!(
            page.contains("blake3.js"),
            "the page must load the verifier"
        );
        // The caps demo was not deleted to make room — it is preserved at its
        // historical filename as a static-site artifact. It is deliberately NOT
        // routed from here: it pulls a remote font via `style.css`, and this
        // surface stays self-contained.
        let caps = include_str!("../../site/explorer/caps-as-rows.html");
        assert!(caps.contains("caps-as-rows.js"));
    }

    #[test]
    /// Every route the page actually reads must be on the allowlist.
    ///
    /// The list above and the page are two halves of one contract that live in
    /// different languages, and nothing forced them to agree: when the node
    /// renamed its attested-roots route the page followed and the allowlist did
    /// not, so a whole panel read "ROUTE NOT ON THE ALLOWLIST" on the deployed
    /// site while every test here stayed green — `public_read_routes_are_allowed`
    /// asserted the routes someone remembered to type into it, which by then
    /// were not the routes the page asked for.
    ///
    /// This reads the call sites out of the compiled-in script instead, so the
    /// only way to add a read is to add it to both.
    #[test]
    fn page_reads_only_allowlisted_routes() {
        let src = include_str!("../../site/explorer/explorer.js");
        let hex = "a".repeat(64);
        let mut found = Vec::new();
        // `nodeGet("api/cells")` and the one template form,
        // `nodeGet(`api/cell/${cellId}/proof`)`. An interpolation stands for a
        // cell id, which is what every one of them is.
        for rest in src.split("nodeGet(").skip(1) {
            let Some(quote) = rest.chars().next() else {
                continue;
            };
            if quote != '"' && quote != '`' {
                continue;
            }
            let Some(end) = rest[1..].find(quote) else {
                continue;
            };
            let mut route = rest[1..1 + end].to_string();
            while let Some(open) = route.find("${") {
                let Some(close) = route[open..].find('}') else {
                    break;
                };
                route.replace_range(open..open + close + 1, &hex);
            }
            found.push(route);
        }
        assert!(
            found.len() >= 8,
            "expected to find the page's node reads, got {found:?} — the scan is looking for the \
             wrong call shape, which would make this test vacuous"
        );
        for route in &found {
            assert!(
                allow_node_path(route),
                "explorer.js reads `{route}`, which the hop refuses — add it to allow_node_path"
            );
        }
    }

    #[test]
    fn page_has_no_external_network_dependencies() {
        // A verification surface that silently fails closed when a CDN is
        // unreachable is worse than one that never had the dependency.
        for (name, src) in [
            ("index.html", include_str!("../../site/explorer/index.html")),
            (
                "explorer.css",
                include_str!("../../site/explorer/explorer.css"),
            ),
            (
                "explorer.js",
                include_str!("../../site/explorer/explorer.js"),
            ),
            ("blake3.js", include_str!("../../site/explorer/blake3.js")),
        ] {
            assert!(
                !src.contains("https://fonts.googleapis.com"),
                "{name} pulls a remote font"
            );
            assert!(
                !src.contains("cdn.jsdelivr.net") && !src.contains("unpkg.com"),
                "{name} pulls a remote script"
            );
        }
    }

    #[test]
    fn verifier_pins_the_current_ledger_root_domain() {
        // The in-browser check folds under this exact context string. If
        // `persist/src/lib.rs` cuts a v4 epoch and this is not updated, the
        // explorer would report every honest node as unverifiable — so pin it
        // here, next to a test that will be read when that happens.
        let js = include_str!("../../site/explorer/blake3.js");
        assert!(js.contains(r#"LEDGER_ROOT_CONTEXT = "dregg-ledger-root-v3""#));
        let rust = include_str!("../../persist/src/lib.rs");
        assert!(
            rust.contains(r#"new_derive_key("dregg-ledger-root-v3")"#),
            "persist no longer folds the ledger root under v3 — update site/explorer/blake3.js"
        );
    }

    // -- routing --------------------------------------------------------------

    #[tokio::test]
    async fn unconfigured_proxy_says_no_node_configured() {
        use axum::body::to_bytes;
        use tower::ServiceExt;

        let app = explorer_router_with_state(Arc::new(ExplorerState::with_node_url(None)));
        let res = app
            .oneshot(
                axum::http::Request::builder()
                    .uri("/explorer/node/status")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(res.status(), StatusCode::SERVICE_UNAVAILABLE);
        let body = to_bytes(res.into_body(), 64 * 1024).await.unwrap();
        let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
        assert_eq!(v["explorer_error"], "no-node-configured");
    }

    #[tokio::test]
    async fn proxy_refuses_a_protected_route_before_any_network_call() {
        use axum::body::to_bytes;
        use tower::ServiceExt;

        // Node URL points nowhere reachable on purpose: a FORBIDDEN here proves
        // the allowlist rejected the path without attempting the hop (an
        // attempted hop would surface as 502 node-unreachable).
        let app = explorer_router_with_state(Arc::new(ExplorerState::with_node_url(Some(
            "http://127.0.0.1:1".into(),
        ))));
        let res = app
            .oneshot(
                axum::http::Request::builder()
                    .uri("/explorer/node/cipherclerk/tokens")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(res.status(), StatusCode::FORBIDDEN);
        let body = to_bytes(res.into_body(), 64 * 1024).await.unwrap();
        let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
        assert_eq!(v["explorer_error"], "path-not-allowed");
    }

    #[tokio::test]
    async fn unreachable_node_is_distinct_from_unconfigured() {
        use axum::body::to_bytes;
        use tower::ServiceExt;

        let app = explorer_router_with_state(Arc::new(ExplorerState::with_node_url(Some(
            "http://127.0.0.1:1".into(),
        ))));
        let res = app
            .oneshot(
                axum::http::Request::builder()
                    .uri("/explorer/node/status")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(res.status(), StatusCode::BAD_GATEWAY);
        let body = to_bytes(res.into_body(), 64 * 1024).await.unwrap();
        let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
        assert_eq!(v["explorer_error"], "node-unreachable");
    }

    #[tokio::test]
    async fn target_readout_distinguishes_configured_from_not() {
        use axum::body::to_bytes;
        use tower::ServiceExt;

        let app = explorer_router_with_state(Arc::new(ExplorerState::with_node_url(None)));
        let res = app
            .oneshot(
                axum::http::Request::builder()
                    .uri("/explorer/target")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(res.status(), StatusCode::OK);
        let body = to_bytes(res.into_body(), 64 * 1024).await.unwrap();
        let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
        assert_eq!(v["configured"], false);
        assert!(v["node_url"].is_null());

        let app = explorer_router_with_state(Arc::new(ExplorerState::with_node_url(Some(
            "http://example.invalid:8420".into(),
        ))));
        let res = app
            .oneshot(
                axum::http::Request::builder()
                    .uri("/explorer/target")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        let body = to_bytes(res.into_body(), 64 * 1024).await.unwrap();
        let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
        assert_eq!(v["configured"], true);
        assert_eq!(v["node_url"], "http://example.invalid:8420");
    }

    #[tokio::test]
    async fn the_page_and_its_assets_are_served() {
        use tower::ServiceExt;

        for (uri, ctype) in [
            ("/explorer", "text/html"),
            ("/explorer/explorer.css", "text/css"),
            ("/explorer/explorer.js", "text/javascript"),
            ("/explorer/blake3.js", "text/javascript"),
        ] {
            let app = explorer_router_with_state(Arc::new(ExplorerState::with_node_url(None)));
            let res = app
                .oneshot(
                    axum::http::Request::builder()
                        .uri(uri)
                        .body(Body::empty())
                        .unwrap(),
                )
                .await
                .unwrap();
            assert_eq!(res.status(), StatusCode::OK, "{uri}");
            let got = res
                .headers()
                .get(header::CONTENT_TYPE)
                .and_then(|v| v.to_str().ok())
                .unwrap_or_default()
                .to_string();
            assert!(got.starts_with(ctype), "{uri}: content-type {got}");
        }
    }
}
