//! End-to-end integration: drive the *assembled* gateway over a **real TCP socket**.
//!
//! The in-module unit tests exercise the pure handlers with an explicit subject. These
//! tests stand the whole [`Gateway`] up on an ephemeral port through the real
//! [`http_serve`] serve loop and speak raw HTTP/1.1 at it — so the socket parse, the
//! auth resolution, the router, and every store are exercised together, the way a
//! client hits it. They cover the full machine lifecycle, cross-tenant isolation, the
//! cap-gated write path (publish + launch + idempotency), microsite serving, malformed
//! input, the on-demand-TLS `ask`, and concurrent multi-tenant traffic — and both auth
//! postures (a verified `dga1_` credential, and the trusted-header proxy posture).

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;

use host_gateway::{
    Gateway, MachineStore, MachinesHandler, Microsite, SandboxLauncher, SiteRegistry, SubjectAuth,
};
use http_serve::{Limits, serve_on};
use starbridge_domains::{ChallengeMethod, DomainBinding, DomainRegistry};

const ALICE: &str = "dregg:alice";
const BOB: &str = "dregg:bob";

/// A parsed HTTP response.
struct Resp {
    status: u16,
    body: String,
}

/// Stand a gateway up on an ephemeral port; return its address. The listener serves
/// forever on a background thread (each request is `Connection: close`).
fn serve(gateway: Gateway) -> std::net::SocketAddr {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind");
    let addr = listener.local_addr().unwrap();
    let service = gateway.into_service();
    std::thread::spawn(move || {
        let _ = serve_on(listener, service, Limits::default());
    });
    addr
}

/// Send one raw HTTP/1.1 request and read the full response.
fn send(
    addr: std::net::SocketAddr,
    method: &str,
    host: &str,
    target: &str,
    headers: &[(&str, &str)],
    body: &[u8],
) -> Resp {
    let mut conn = TcpStream::connect(addr).expect("connect");
    let mut head = format!(
        "{method} {target} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nContent-Length: {}\r\n",
        body.len()
    );
    for (n, v) in headers {
        head.push_str(&format!("{n}: {v}\r\n"));
    }
    head.push_str("\r\n");
    conn.write_all(head.as_bytes()).unwrap();
    conn.write_all(body).unwrap();
    conn.flush().unwrap();
    let mut raw = Vec::new();
    conn.read_to_end(&mut raw).unwrap();
    let text = String::from_utf8_lossy(&raw);
    let status = text
        .split_whitespace()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let body = text.splitn(2, "\r\n\r\n").nth(1).unwrap_or("").to_string();
    Resp { status, body }
}

fn get(addr: std::net::SocketAddr, host: &str, target: &str, subject: Option<&str>) -> Resp {
    let hdrs: Vec<(&str, &str)> = subject
        .map(|s| vec![("x-dregg-subject", s)])
        .unwrap_or_default();
    send(addr, "GET", host, target, &hdrs, &[])
}

/// A gateway with a published site, a verified custom domain, a real sandbox launcher,
/// and the trusted-header posture (clean distinct subjects for the isolation tests).
fn trusted_gateway() -> Gateway {
    let sites = Arc::new(SiteRegistry::new("dregg.net"));
    sites
        .publish(Microsite::new("blog", ALICE).with("/index.html", "<h1>alice blog</h1>"))
        .unwrap();
    let domains = Arc::new(DomainRegistry::new());
    domains.adopt(DomainBinding::verified(
        "www.acme.com",
        "blog",
        ALICE,
        ChallengeMethod::Txt,
        "nonce",
        1,
    ));
    let store = Arc::new(MachineStore::new());
    let machines = MachinesHandler::over(store, Arc::new(SandboxLauncher::new()));
    Gateway::new(
        sites,
        domains,
        machines,
        SubjectAuth::trusted_header("x-dregg-subject"),
    )
}

fn create_body(image: &str) -> Vec<u8> {
    serde_json::to_vec(&serde_json::json!({
        "name": "web",
        "config": { "guest": { "cpus": 1, "memory_mb": 256, "image": image }, "region": "iad" }
    }))
    .unwrap()
}

#[test]
fn full_machine_lifecycle_over_the_socket() {
    let addr = serve(trusted_gateway());

    // Create (owner Alice) -> 201, real sandbox lease launched.
    let created = send(
        addr,
        "POST",
        "gw",
        "/v1/apps/app1/machines",
        &[("x-dregg-subject", ALICE)],
        &create_body("workload:agent"),
    );
    assert_eq!(created.status, 201, "{}", created.body);
    let m: serde_json::Value = serde_json::from_str(&created.body).unwrap();
    let id = m["id"].as_str().unwrap().to_string();
    assert_eq!(m["state"], "started");
    assert!(id.starts_with("mch_"));

    // List (Alice) -> 1.
    let listed = get(addr, "gw", "/v1/apps/app1/machines", Some(ALICE));
    assert_eq!(listed.status, 200);
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&listed.body)
            .unwrap()
            .as_array()
            .unwrap()
            .len(),
        1
    );

    // Stop -> stopped, Start -> started.
    let stopped = send(
        addr,
        "POST",
        "gw",
        &format!("/v1/apps/app1/machines/{id}/stop"),
        &[("x-dregg-subject", ALICE)],
        &[],
    );
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&stopped.body).unwrap()["state"],
        "stopped"
    );
    let started = send(
        addr,
        "POST",
        "gw",
        &format!("/v1/apps/app1/machines/{id}/start"),
        &[("x-dregg-subject", ALICE)],
        &[],
    );
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&started.body).unwrap()["state"],
        "started"
    );

    // Delete -> destroyed, then gone.
    let del = send(
        addr,
        "DELETE",
        "gw",
        &format!("/v1/apps/app1/machines/{id}"),
        &[("x-dregg-subject", ALICE)],
        &[],
    );
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&del.body).unwrap()["state"],
        "destroyed"
    );
    assert_eq!(
        get(
            addr,
            "gw",
            &format!("/v1/apps/app1/machines/{id}"),
            Some(ALICE)
        )
        .status,
        404
    );
}

#[test]
fn cross_tenant_isolation_over_the_socket() {
    let addr = serve(trusted_gateway());
    // Alice creates a machine.
    let created = send(
        addr,
        "POST",
        "gw",
        "/v1/apps/app1/machines",
        &[("x-dregg-subject", ALICE)],
        &create_body("img"),
    );
    let id = serde_json::from_str::<serde_json::Value>(&created.body).unwrap()["id"]
        .as_str()
        .unwrap()
        .to_string();

    // Bob, knowing app+id, cannot read/stop/delete it — every attempt 404.
    for (method, path) in [
        ("GET", format!("/v1/apps/app1/machines/{id}")),
        ("POST", format!("/v1/apps/app1/machines/{id}/stop")),
        ("DELETE", format!("/v1/apps/app1/machines/{id}")),
    ] {
        let r = send(addr, method, "gw", &path, &[("x-dregg-subject", BOB)], &[]);
        assert_eq!(r.status, 404, "{method} {path} by Bob must be 404");
    }
    // And no subject at all is 401.
    assert_eq!(
        get(addr, "gw", &format!("/v1/apps/app1/machines/{id}"), None).status,
        401
    );
    // Alice's machine is untouched.
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(
            &get(
                addr,
                "gw",
                &format!("/v1/apps/app1/machines/{id}"),
                Some(ALICE)
            )
            .body
        )
        .unwrap()["state"],
        "started"
    );
}

#[test]
fn write_path_publish_and_serve_over_the_socket() {
    let addr = serve(trusted_gateway());
    // Publish a new microsite over HTTP (cap-gated: owner = the verified subject).
    let body = serde_json::to_vec(&serde_json::json!({
        "name": "shop",
        "assets": [{ "path": "/index.html", "text": "<h1>bob shop</h1>" }]
    }))
    .unwrap();
    let pub_resp = send(
        addr,
        "POST",
        "gw",
        "/api/sites",
        &[("x-dregg-subject", BOB), ("idempotency-key", "k1")],
        &body,
    );
    assert_eq!(pub_resp.status, 201, "{}", pub_resp.body);
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&pub_resp.body).unwrap()["owner"],
        BOB
    );

    // It is immediately live on its wildcard host.
    let served = get(addr, "shop.dregg.net", "/", None);
    assert_eq!(served.status, 200);
    assert!(served.body.contains("bob shop"), "{}", served.body);

    // A stranger cannot republish it (403 no-takeover).
    let takeover = send(
        addr,
        "POST",
        "gw",
        "/api/sites",
        &[("x-dregg-subject", ALICE)],
        &body,
    );
    assert_eq!(takeover.status, 403);

    // The idempotency key replays (no re-execution): a same-key retry returns 201 again.
    let replay = send(
        addr,
        "POST",
        "gw",
        "/api/sites",
        &[("x-dregg-subject", BOB), ("idempotency-key", "k1")],
        &body,
    );
    assert_eq!(replay.status, 201);
}

#[test]
fn launch_over_the_socket_serves_a_landing_page() {
    let addr = serve(trusted_gateway());
    let body = serde_json::to_vec(&serde_json::json!({
        "slug": "moon", "title": "Moon", "blurb": "to the moon", "metadata": { "symbol": "MOON" }
    }))
    .unwrap();
    let r = send(
        addr,
        "POST",
        "gw",
        "/api/launches",
        &[("x-dregg-subject", ALICE)],
        &body,
    );
    assert_eq!(r.status, 201, "{}", r.body);
    let v: serde_json::Value = serde_json::from_str(&r.body).unwrap();
    assert_eq!(v["landing_host"], "moon.dregg.net");
    // The landing page is live.
    let landing = get(addr, "moon.dregg.net", "/", None);
    assert_eq!(landing.status, 200);
    assert!(landing.body.contains("Moon"));
    // metadata.json serves and is content-addressed.
    assert_eq!(
        get(addr, "moon.dregg.net", "/metadata.json", None).status,
        200
    );
}

#[test]
fn malformed_and_edge_inputs_do_not_crash_the_gateway() {
    let addr = serve(trusted_gateway());
    // Malformed JSON create body -> 400, connection still usable afterwards.
    let bad = send(
        addr,
        "POST",
        "gw",
        "/v1/apps/app1/machines",
        &[("x-dregg-subject", ALICE)],
        b"{not json",
    );
    assert_eq!(bad.status, 400, "{}", bad.body);
    // Unknown path -> 404.
    assert_eq!(get(addr, "gw", "/nope", None).status, 404);
    // Wildcard host, unknown asset -> 404.
    assert_eq!(
        get(addr, "blog.dregg.net", "/missing.html", None).status,
        404
    );
    // The gateway is still healthy after the bad requests.
    assert_eq!(get(addr, "gw", "/healthz", None).status, 200);
}

#[test]
fn on_demand_tls_ask_over_the_socket() {
    let addr = serve(trusted_gateway());
    assert_eq!(
        get(addr, "gw", "/ask?domain=blog.dregg.net", None).status,
        200
    );
    assert_eq!(
        get(addr, "gw", "/ask?domain=www.acme.com", None).status,
        200
    );
    assert_eq!(
        get(addr, "gw", "/ask?domain=evil.example.com", None).status,
        404
    );
}

#[test]
fn concurrent_multi_tenant_creates_stay_isolated() {
    let addr = serve(trusted_gateway());
    let mut handles = Vec::new();
    for (i, subject) in [(0, ALICE), (1, BOB), (2, ALICE), (3, BOB)] {
        let app = format!("app{i}");
        handles.push(std::thread::spawn(move || {
            let r = send(
                addr,
                "POST",
                "gw",
                &format!("/v1/apps/{app}/machines"),
                &[("x-dregg-subject", subject)],
                &create_body("img"),
            );
            assert_eq!(r.status, 201);
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    // Each owner sees exactly their own machines via the cap-scoped read.
    let alice = get(addr, "gw", "/api/machines", Some(ALICE));
    let bob = get(addr, "gw", "/api/machines", Some(BOB));
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&alice.body)
            .unwrap()
            .as_array()
            .unwrap()
            .len(),
        2
    );
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&bob.body)
            .unwrap()
            .as_array()
            .unwrap()
            .len(),
        2
    );
    // No leakage: Bob's read never contains Alice's subject-owned records (checked by count above);
    // the friendly status reports 4 machines total.
    let status = get(addr, "gw", "/status", None);
    assert!(status.body.contains("\"machines\":4"), "{}", status.body);
}

#[test]
fn verified_credential_posture_over_the_socket() {
    use dregg_agent::cred::RootKey;
    use webauth_core::config::WebAuthConfig;
    use webauth_core::grant::mint_caps;

    let root = RootKey::from_seed([7u8; 32]);
    let cfg = WebAuthConfig {
        root_pubkey_hex: Some(root.public().to_hex()),
        ..WebAuthConfig::default()
    };
    let token = mint_caps(&root, ["console-read"], None).encode();
    let subject = webauth_core::subject_of(&token).unwrap();

    let sites = Arc::new(SiteRegistry::new("dregg.net"));
    sites
        .publish(Microsite::new("mine", &subject).with("/index.html", "hi"))
        .unwrap();
    let gateway = Gateway::new(
        sites,
        Arc::new(DomainRegistry::new()),
        MachinesHandler::new(),
        SubjectAuth::verified(cfg, "console-read"),
    );
    let addr = serve(gateway);
    let bearer = format!("Bearer {token}");

    // A genuine credential resolves its subject and sees its own site.
    let mine = send(
        addr,
        "GET",
        "gw",
        "/api/sites",
        &[("authorization", &bearer)],
        &[],
    );
    assert_eq!(mine.status, 200, "{}", mine.body);
    assert!(mine.body.contains("mine"), "{}", mine.body);

    // No credential -> fail closed (401).
    assert_eq!(get(addr, "gw", "/api/sites", None).status, 401);

    // A create under the verified credential is owner-scoped to its subject.
    let created = send(
        addr,
        "POST",
        "gw",
        "/v1/apps/app1/machines",
        &[("authorization", &bearer)],
        &create_body("img"),
    );
    assert_eq!(created.status, 201, "{}", created.body);
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&created.body).unwrap()["owner"],
        subject
    );
}
