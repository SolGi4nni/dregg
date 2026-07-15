//! The assembled fly-compat host gateway — **one serving block for every surface**.
//!
//! [`Gateway::handle`] classifies each inbound request and dispatches it:
//!
//! 1. **Static microsite data plane (by `Host`)** — if the `Host` resolves to a
//!    published wildcard site (`<name>.<apex>`) or a *verified* custom domain
//!    ([`starbridge_domains::DomainRegistry::site_for_host`]), every path serves that
//!    site's content-addressed assets. A tenant host never exposes the control API.
//! 2. **On-demand-TLS `ask` (`/ask`)** — the cert-issuance gate a reverse proxy calls
//!    before minting a certificate: `200` for a published wildcard host OR a domain
//!    proven through [`starbridge_domains::DomainRegistry::is_verified`], else `404`.
//!    **One gateway block serves any verified host.**
//! 3. **The cap-scoped console reads (`/api/*`)** — [`crate::api::ApiHandler`], scoped
//!    to the subject the gateway *verifies* from the presented credential.
//! 4. **The fly machines API (`/v1/apps/{app}/machines...`)** —
//!    [`crate::machines::MachinesHandler`], creates owner-scoped to the verified subject.
//! 5. **Friendly surfaces** — `/`, `/status`, `/healthz`.
//!
//! The whole thing runs on the resident [`http_serve`] hardened serve loop via
//! [`Gateway::into_service`] + [`http_serve::serve_http`].

use std::sync::Arc;

use http_serve::{HttpMethod, ServeRequest, WebResponse};

use starbridge_domains::DomainRegistry;

use crate::api::ApiHandler;
use crate::auth::SubjectAuth;
use crate::machines::MachinesHandler;
use crate::microsite::SiteRegistry;
use crate::observe::{NullObserver, Observer, RequestEvent};
use crate::route;
use crate::util::request_id;
use crate::write::WriteHandler;

/// The assembled gateway. Holds the resident registries + sub-handlers and the
/// subject-auth posture; [`handle`](Gateway::handle) routes one request.
pub struct Gateway {
    sites: Arc<SiteRegistry>,
    domains: Arc<DomainRegistry>,
    api: ApiHandler,
    write: WriteHandler,
    machines: MachinesHandler,
    auth: SubjectAuth,
    observer: Arc<dyn Observer>,
    apex: String,
}

impl Gateway {
    /// Assemble the gateway.
    ///
    /// * `sites` — the wildcard microsite data plane (and `/api/sites` source);
    /// * `domains` — the verified custom-domain resolver (and the `ask` `is_verified`);
    /// * `machines` — the fly machines handler (its store is the `/api/machines` source);
    /// * `auth` — how the cap-scope subject is established (verify a credential, or trust
    ///   an internal proxy header);
    /// * server / agent / billing sources are attached on the returned `Gateway`'s
    ///   [`api_mut`](Gateway::api_mut) if the control planes expose them.
    ///
    /// The `/api/machines` read binds to the SAME store the machines handler writes.
    pub fn new(
        sites: Arc<SiteRegistry>,
        domains: Arc<DomainRegistry>,
        machines: MachinesHandler,
        auth: SubjectAuth,
    ) -> Gateway {
        let apex = sites.apex().to_string();
        let api = ApiHandler::new(
            Arc::clone(&sites),
            Arc::clone(&domains),
            Arc::clone(machines.store()),
        );
        let write = WriteHandler::new(Arc::clone(&sites));
        Gateway {
            sites,
            domains,
            api,
            write,
            machines,
            auth,
            observer: Arc::new(NullObserver),
            apex,
        }
    }

    /// Attach a request [`Observer`] (structured logging / metrics). Builder-style,
    /// before serving. Default: [`NullObserver`] (silent).
    pub fn with_observer(mut self, observer: Arc<dyn Observer>) -> Gateway {
        self.observer = observer;
        self
    }

    /// Mutable access to the console-reads handler, to attach server / agent / billing
    /// sources (builder-style, before serving).
    pub fn api_mut(&mut self) -> &mut ApiHandler {
        &mut self.api
    }

    /// The deployment's configured hosting apex.
    pub fn apex(&self) -> &str {
        &self.apex
    }

    /// Whether `host` should be served as a static site — a published wildcard host or a
    /// verified custom domain (the routing decision that keeps the control API off tenant
    /// hosts).
    pub fn serves_site_host(&self, host: &str) -> bool {
        self.sites.serves_host(host) || self.domains.site_for_host(host).is_some()
    }

    /// The on-demand-TLS `ask` decision for `host`: a cert should be minted iff the host
    /// is a published wildcard site OR a domain proven against DNS
    /// ([`DomainRegistry::is_verified`]). Never mints for an unverified / squatted domain.
    pub fn cert_ok(&self, host: &str) -> bool {
        self.sites.serves_host(host) || self.domains.is_verified(host)
    }

    /// Route + serve one request, emitting a structured [`RequestEvent`] (with a minted
    /// request id) to the observer on the way out.
    pub fn handle(&self, req: &ServeRequest) -> WebResponse {
        let rid = request_id();
        let started = std::time::Instant::now();
        let path = req.target.split('?').next().unwrap_or(&req.target);
        let mut authenticated = false;
        let resp = self.route(req, path, &mut authenticated);
        self.observer.on_request(&RequestEvent {
            request_id: &rid,
            method: req.method,
            path,
            host: &req.host,
            authenticated,
            status: resp.status,
            elapsed_us: started.elapsed().as_micros(),
        });
        resp
    }

    /// The routing core (`handle` wraps it with observability). `authenticated` is set
    /// when a request resolved a verified subject.
    fn route(&self, req: &ServeRequest, path: &str, authenticated: &mut bool) -> WebResponse {
        // 1. A tenant site host serves its content on every path (control API excluded).
        if self.serves_site_host(&req.host) {
            return self.serve_site(&req.host, &req.target);
        }

        // 2. The on-demand-TLS ask.
        if path == "/ask" {
            return self.ask(req);
        }

        // 3. The cap-gated write path (POST/PUT/DELETE on the hosting primitives).
        if WriteHandler::serves(req.method, path) {
            let subject = self.auth.resolve(req);
            *authenticated = subject.is_some();
            let idem = req.header("idempotency-key");
            return self.write.respond(
                req.method,
                &req.target,
                &req.body,
                subject.as_deref(),
                idem,
            );
        }

        // 4. The cap-scoped console reads.
        if ApiHandler::serves_path(path) {
            let subject = self.auth.resolve(req);
            *authenticated = subject.is_some();
            return self
                .api
                .respond(req.method, &req.target, subject.as_deref());
        }

        // 5. The fly machines API.
        if route::serves_path(path) {
            let subject = self.auth.resolve(req);
            *authenticated = subject.is_some();
            return self
                .machines
                .respond(req.method, &req.target, &req.body, subject.as_deref());
        }

        // 6. Friendly surfaces.
        match (req.method, path.trim_end_matches('/')) {
            (HttpMethod::Get, "") => self.landing(),
            (HttpMethod::Get, "/status") | (HttpMethod::Get, "/v1") => self.status(),
            (HttpMethod::Get, "/health") | (HttpMethod::Get, "/healthz") => {
                WebResponse::json(br#"{"status":"ok"}"#.to_vec())
            }
            _ => WebResponse::error(404, "not found"),
        }
    }

    /// Serve a static site by host (a verified custom domain routes to its bound site;
    /// else the wildcard `<name>.<apex>` path).
    fn serve_site(&self, host: &str, target: &str) -> WebResponse {
        let path = target.split('?').next().unwrap_or(target);
        match self.domains.site_for_host(host) {
            Some(name) => match self.sites.get(&name) {
                Some(site) => site.serve(path),
                None => WebResponse::error(404, "bound site not published"),
            },
            None => self.sites.resolve(host, path),
        }
    }

    /// The on-demand-TLS ask. A reverse proxy passes `?domain=<host>`; absent, the
    /// request `Host` is used. `200` (issue) iff [`cert_ok`](Gateway::cert_ok).
    fn ask(&self, req: &ServeRequest) -> WebResponse {
        let domain = query_param(&req.target, "domain")
            .filter(|d| !d.is_empty())
            .unwrap_or_else(|| req.host.clone());
        if self.cert_ok(&domain) {
            WebResponse::json(br#"{"ok":true}"#.to_vec())
        } else {
            WebResponse::error(
                404,
                format!("no certificate for unverified host `{domain}`"),
            )
        }
    }

    /// The friendly HTML landing for the gateway control host.
    fn landing(&self) -> WebResponse {
        let body = format!(
            "<!doctype html><meta charset=utf-8><title>host gateway</title>\
             <h1>host gateway</h1><p>fly-compatible machines API + cap-scoped reads. \
             hosting apex <code>{}</code>.</p>",
            self.apex
        );
        WebResponse {
            status: 200,
            content_type: "text/html; charset=utf-8".to_string(),
            body: body.into_bytes(),
        }
    }

    /// The gateway status as JSON (apex + live registry counts).
    fn status(&self) -> WebResponse {
        let body = serde_json::json!({
            "status": "ok",
            "apex": self.apex,
            "sites": self.sites.names().len(),
            "domains": self.domains.list().len(),
            "machines": self.machines.store().count(),
        });
        WebResponse::json(body.to_string().into_bytes())
    }

    /// Turn the gateway into an `Fn(&ServeRequest) -> WebResponse` service for
    /// [`http_serve::serve_http`] / [`http_serve::serve_on`].
    pub fn into_service(self) -> impl Fn(&ServeRequest) -> WebResponse + Send + Sync + 'static {
        move |req: &ServeRequest| self.handle(req)
    }
}

/// Extract the first value of query parameter `key` from a request target
/// (percent-decoding is not applied — a domain has no reserved chars needing it).
fn query_param(target: &str, key: &str) -> Option<String> {
    let (_, query) = target.split_once('?')?;
    for pair in query.split('&') {
        if let Some((k, v)) = pair.split_once('=') {
            if k == key {
                return Some(v.to_string());
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machines::CreateMachineRequest;
    use crate::microsite::Microsite;
    use starbridge_domains::{ChallengeMethod, DomainBinding};

    const ALICE: &str = "dregg:alice";

    fn gateway() -> Gateway {
        let sites = Arc::new(SiteRegistry::new("dregg.net"));
        sites
            .publish(Microsite::new("blog", ALICE).with("/index.html", "<h1>hi</h1>"))
            .unwrap();
        let domains = Arc::new(DomainRegistry::new());
        // A verified custom domain routing to the blog site.
        domains.adopt(DomainBinding::verified(
            "www.acme.com",
            "blog",
            ALICE,
            ChallengeMethod::Txt,
            "nonce",
            1,
        ));
        Gateway::new(
            sites,
            domains,
            MachinesHandler::new(),
            SubjectAuth::trusted_header("x-dregg-subject"),
        )
    }

    fn req(
        method: HttpMethod,
        host: &str,
        target: &str,
        headers: Vec<(&str, &str)>,
    ) -> ServeRequest {
        ServeRequest {
            method,
            host: host.into(),
            target: target.into(),
            body: Vec::new(),
            headers: headers
                .into_iter()
                .map(|(n, v)| (n.to_ascii_lowercase(), v.to_string()))
                .collect(),
        }
    }

    #[test]
    fn wildcard_host_serves_the_site() {
        let g = gateway();
        let resp = g.handle(&req(HttpMethod::Get, "blog.dregg.net", "/", vec![]));
        assert_eq!(resp.status, 200);
        assert_eq!(resp.body, b"<h1>hi</h1>");
    }

    #[test]
    fn verified_custom_domain_routes_to_its_bound_site() {
        let g = gateway();
        let resp = g.handle(&req(HttpMethod::Get, "www.acme.com", "/", vec![]));
        assert_eq!(resp.status, 200);
        assert_eq!(resp.body, b"<h1>hi</h1>");
    }

    #[test]
    fn on_demand_tls_ask_issues_only_for_verified_hosts() {
        let g = gateway();
        // Published wildcard host → issue.
        assert_eq!(
            g.handle(&req(
                HttpMethod::Get,
                "gw",
                "/ask?domain=blog.dregg.net",
                vec![]
            ))
            .status,
            200
        );
        // Verified custom domain → issue.
        assert_eq!(
            g.handle(&req(
                HttpMethod::Get,
                "gw",
                "/ask?domain=www.acme.com",
                vec![]
            ))
            .status,
            200
        );
        // Unverified / squatted host → refuse (no cert).
        assert_eq!(
            g.handle(&req(
                HttpMethod::Get,
                "gw",
                "/ask?domain=evil.example.com",
                vec![]
            ))
            .status,
            404
        );
        // An unpublished wildcard name → refuse.
        assert_eq!(
            g.handle(&req(
                HttpMethod::Get,
                "gw",
                "/ask?domain=nope.dregg.net",
                vec![]
            ))
            .status,
            404
        );
    }

    #[test]
    fn control_plane_routes_api_and_fly_and_friendly() {
        let g = gateway();

        // Friendly.
        assert_eq!(
            g.handle(&req(HttpMethod::Get, "gw", "/healthz", vec![]))
                .status,
            200
        );
        let status = g.handle(&req(HttpMethod::Get, "gw", "/status", vec![]));
        assert_eq!(status.status, 200);
        assert!(status.body_str().contains("dregg.net"));

        // The cap-scoped reads: fail closed without a subject, scoped with one.
        assert_eq!(
            g.handle(&req(HttpMethod::Get, "gw", "/api/sites", vec![]))
                .status,
            401
        );
        let scoped = g.handle(&req(
            HttpMethod::Get,
            "gw",
            "/api/sites",
            vec![("x-dregg-subject", ALICE)],
        ));
        assert_eq!(scoped.status, 200);
        assert!(scoped.body_str().contains("blog"));

        // The fly machines API: a create needs the verified subject, then lists it.
        let create = ServeRequest {
            method: HttpMethod::Post,
            host: "gw".into(),
            target: "/v1/apps/app1/machines".into(),
            body: serde_json::to_vec(&CreateMachineRequest::default()).unwrap(),
            headers: vec![("x-dregg-subject".into(), ALICE.into())],
        };
        assert_eq!(g.handle(&create).status, 201);
        // The list is now owner-scoped: it requires the verified subject (401 without).
        assert_eq!(
            g.handle(&req(
                HttpMethod::Get,
                "gw",
                "/v1/apps/app1/machines",
                vec![]
            ))
            .status,
            401
        );
        let listed = g.handle(&req(
            HttpMethod::Get,
            "gw",
            "/v1/apps/app1/machines",
            vec![("x-dregg-subject", ALICE)],
        ));
        assert_eq!(listed.status, 200);
        // And that machine shows up on the owner's cap-scoped /api/machines.
        let mine = g.handle(&req(
            HttpMethod::Get,
            "gw",
            "/api/machines",
            vec![("x-dregg-subject", ALICE)],
        ));
        assert!(mine.body_str().contains("app1"));
    }

    #[test]
    fn a_tenant_site_host_does_not_expose_the_control_api() {
        let g = gateway();
        // `/api/sites` on a tenant site host is served as a site path (404 asset), NOT
        // the control API — the control plane is only on the gateway host.
        let resp = g.handle(&req(
            HttpMethod::Get,
            "blog.dregg.net",
            "/api/sites",
            vec![("x-dregg-subject", ALICE)],
        ));
        assert_eq!(resp.status, 404);
        assert!(!resp.body_str().contains("content_root"));
    }
}
