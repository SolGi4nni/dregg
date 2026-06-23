//! **THE CAP-GATED HTTP(S) PROTOCOL HANDLER — the real http(s) byte socket, owned
//! by the embedder through the net-cap gate.**
//!
//! ## What the forbidden-scheme fork unlocked
//!
//! Servo's `net` crate normally blocks an embedder from registering a
//! `ProtocolHandler` for `http`/`https` (`FORBIDDEN_SCHEMES`), so the http(s) byte
//! socket was always servo's internal hyper — the [`netcap_connector`](crate::netcap_connector)
//! could bind only the *connect decision*, never the bytes. The vendored
//! `servo-net` fork (`servo-render/vendor/servo-net`, `[patch.crates-io]`) removes
//! `http`/`https` from `FORBIDDEN_SCHEMES` and makes `scheme_fetch` consult an
//! embedder-registered handler FIRST for those schemes. THIS module is that
//! handler: a real [`ProtocolHandler`](servo::protocol_handler::ProtocolHandler)
//! that owns the http(s) socket and routes it through the cap gate.
//!
//! ## The two teeth, in order (HONEST)
//!
//! 1. **THE CAP, AT THE SOCKET.** [`CapGatedHttpHandler::load`] first runs the
//!    held [`SurfaceCapability`]'s connect decision through the
//!    [`NetcapConnector`](crate::netcap_connector::NetcapConnector) — the SAME
//!    `Netlayer::dial` gate `netcap_connector` proves. A cap-denied origin returns
//!    a `network_error` and **no byte socket is ever opened** (`Netlayer::dial` is
//!    never reached); the page sees the refusal, never the resource. A cap-admitted
//!    origin proceeds to the byte fetch.
//! 2. **THE REAL BYTE SOCKET.** For a cap-admitted origin the handler opens a REAL
//!    `std::net::TcpStream`, writes a genuine HTTP/1.1 `GET`, reads the response,
//!    splits status/headers/body, and hands servo a [`Response`] with the body +
//!    `Content-Type` — which servo lays out and SWGL rasterizes. For `https://` the
//!    handler first drives a real `rustls` TLS handshake over that same socket and
//!    speaks the GET over the encrypted stream. This socket is the EMBEDDER's, opened
//!    only after the cap gate admitted the origin — not servo's hyper.
//!
//! ## The TLS leg (`https://`) — same socket, same cap gate first
//!
//! For a cap-admitted **`https://`** origin the handler does the IDENTICAL cap gate
//! first (Tooth 1), opens the SAME real `std::net::TcpStream`, then wraps it in a
//! `rustls::ClientConnection` keyed on the SNI host and does the HTTP/1.1 GET over the
//! encrypted `StreamOwned` ([`https_get_over_real_socket`]). `rustls` is the one
//! already in servo-net's graph (the `aws-lc-rs` provider), so this adds no second TLS
//! stack. The PRODUCTION verifier trusts the Mozilla CA set (`webpki-roots`) — a
//! cap-admitted *public* https origin is verified against real roots, no danger-accept.
//! A test may register an EXTRA trusted root via [`CapGatedHttpHandler::trust_extra_root_der`]
//! (its self-signed cert), which is added to the SAME genuine rustls verifier — not a
//! verification bypass. Plain `http://` stays on the existing plaintext path.
//!
//! The deliverable exercises the full real path for both schemes: cap gate → real
//! socket (→ TLS handshake for https) → real bytes → servo layout → SWGL raster → PNG.

#![cfg(feature = "libservo")]

use std::future::Future;
use std::io::{Read, Write};
use std::net::TcpStream;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use rustls::pki_types::{CertificateDer, ServerName};
use rustls::{ClientConfig, ClientConnection, RootCertStore, StreamOwned};

use servo::protocol_handler::{
    DoneChannel, FetchContext, NetworkError, ProtocolHandler, Request, ResourceFetchTiming,
    Response, ResponseBody,
};
use servo::ServoUrl;

use dregg_captp::netlayer::InProcessNetlayer;
use starbridge_web_surface::SurfaceCapability;

use crate::netcap_connector::{block_on, ConnectOutcome, NetcapConnector};

/// The cap-gated http(s) protocol handler servo's `scheme_fetch` routes http/https
/// through (under the vendored `servo-net` fork). Holds the surface authority + the
/// audited netlayer connector; every load discharges the held cap at the socket.
pub struct CapGatedHttpHandler {
    /// The per-render authority + audited connector, behind a `Mutex` so a SINGLE
    /// handler (registered once on the one-per-process `Servo` engine) can be
    /// re-pointed at a new surface/origin for each render — servo's
    /// `servo_config::opts` is a process `OnceCell`, so only one engine (hence one
    /// registered handler) exists per process; [`reconfigure`](Self::reconfigure)
    /// swaps the held cap + reachable peers before each render.
    active: Mutex<Active>,
    /// The net-cap outcomes this handler produced, newest last — the audit trail the
    /// test reads back to prove WHICH gate an origin hit.
    outcomes: Mutex<Vec<ConnectOutcome>>,
    /// The last fetched URL → its fetched byte length, for the test's status line.
    last_fetch: Mutex<Option<(String, usize)>>,
    /// EXTRA https trust anchors (DER) the embedder added BEYOND the Mozilla CA set —
    /// e.g. a test's self-signed cert. These are added to the SAME genuine rustls
    /// verifier (`RootCertStore`), so the handshake is real cert validation, NOT a
    /// danger-accept bypass; production https origins still verify against the public
    /// `webpki-roots`. Empty by default (a public https origin uses only the real roots).
    extra_roots: Mutex<Vec<CertificateDer<'static>>>,
    /// Whether the last https fetch completed a real TLS handshake (set true the moment
    /// `rustls` reports the connection negotiated) — the test reads this to prove the
    /// bytes came over an encrypted socket, not plaintext.
    last_tls_handshake: Mutex<bool>,
}

/// The swappable per-render state: the held surface cap + the audited connector
/// over a fabric in which the render's reachable peers have joined.
struct Active {
    surface: SurfaceCapability,
    connector: NetcapConnector<InProcessNetlayer>,
}

fn build_active(surface: SurfaceCapability, seed_origins: &[String]) -> Active {
    use crate::netcap_connector::origin_to_peer;
    use dregg_captp::netlayer::InProcessFabric;
    let fabric = InProcessFabric::new();
    // Our own node (the page's dialer identity) — a fixed id in the keyspace.
    let me = fabric.join([0x5e; 32]);
    for o in seed_origins {
        let _ = fabric.join(origin_to_peer(o));
    }
    Active { surface, connector: NetcapConnector::new(me) }
}

impl CapGatedHttpHandler {
    /// Build the handler for `surface`, over an in-process netlayer fabric in which
    /// the surface's authorized origins' peers have joined (so a cap-admitted origin
    /// dials a reachable peer through the audited netlayer; an unauthorized origin is
    /// refused at the connector before any dial). Mirrors `webview::build_cap_gate`.
    pub fn new(surface: SurfaceCapability, seed_origins: &[String]) -> Self {
        CapGatedHttpHandler {
            active: Mutex::new(build_active(surface, seed_origins)),
            outcomes: Mutex::new(Vec::new()),
            last_fetch: Mutex::new(None),
            extra_roots: Mutex::new(Vec::new()),
            last_tls_handshake: Mutex::new(false),
        }
    }

    /// Add an EXTRA trusted https root certificate (DER), BEYOND the Mozilla CA set, to
    /// the genuine rustls verifier this handler builds per https fetch. Used by a test
    /// to trust its local self-signed server cert — the handshake is then REAL cert
    /// validation against this root (the same `RootCertStore` path a public CA takes),
    /// not a `danger_accept_invalid_certs` bypass. Survives `reconfigure` (the trust
    /// set is about the embedder's environment, not the per-render surface).
    pub fn trust_extra_root_der(&self, cert_der: Vec<u8>) {
        self.extra_roots
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push(CertificateDer::from(cert_der));
    }

    /// Whether the most recent https fetch completed a real TLS handshake over the
    /// cap-admitted socket (false for plain http or if no https fetch ran). The test
    /// asserts this to prove the bytes crossed an encrypted socket.
    pub fn last_tls_handshake(&self) -> bool {
        *self.last_tls_handshake.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Re-point this handler at a NEW surface + reachable-peer set for the next
    /// render, and clear the audit trail. Used to drive several pages (different
    /// surfaces) through the ONE per-process engine's ONE registered handler.
    pub fn reconfigure(&self, surface: SurfaceCapability, seed_origins: &[String]) {
        *self.active.lock().unwrap_or_else(|e| e.into_inner()) =
            build_active(surface, seed_origins);
        self.outcomes.lock().unwrap_or_else(|e| e.into_inner()).clear();
        *self.last_fetch.lock().unwrap_or_else(|e| e.into_inner()) = None;
        *self.last_tls_handshake.lock().unwrap_or_else(|e| e.into_inner()) = false;
        // NOTE: `extra_roots` is intentionally NOT cleared — the embedder's trust set
        // (e.g. the test's self-signed root) is about the environment, not the
        // per-render surface, and persists across renders.
    }

    /// The net-cap outcomes this handler produced, newest last (the audit trail).
    pub fn outcomes(&self) -> Vec<ConnectOutcome> {
        self.outcomes.lock().unwrap_or_else(|e| e.into_inner()).clone()
    }

    /// The last (url, fetched-byte-length) this handler served — the test's status line.
    pub fn last_fetch(&self) -> Option<(String, usize)> {
        self.last_fetch.lock().unwrap_or_else(|e| e.into_inner()).clone()
    }
}

impl ProtocolHandler for CapGatedHttpHandler {
    /// Resources served by this handler are directly fetchable (so a same-context
    /// `fetch()` of an http(s) resource also routes through this cap-gated path, not
    /// just a top-level navigation). The top-level navigation always reaches
    /// `scheme_fetch` regardless (RequestMode::Navigate), which is the deliverable.
    fn is_fetchable(&self) -> bool {
        true
    }

    fn load<'a>(
        &'a self,
        request: &'a mut Request,
        _done_chan: &mut DoneChannel,
        _context: &FetchContext,
    ) -> Pin<Box<dyn Future<Output = Response> + Send + 'a>> {
        let url = request.current_url();
        debug_assert!(matches!(url.scheme(), "http" | "https"));
        let origin = url.origin().ascii_serialization();

        // ── TOOTH 1: THE CAP, AT THE SOCKET ──────────────────────────────────────
        // Route the connect decision through the audited netlayer. A cap-denied
        // origin is refused HERE — `Netlayer::dial` is never reached, the byte
        // socket is never opened. The page gets a network error, never the resource.
        // (Under the per-render `active` lock, so a `reconfigure` between renders
        // does not race with an in-flight decision.)
        let outcome = {
            let active = self.active.lock().unwrap_or_else(|e| e.into_inner());
            block_on(active.connector.connect(&active.surface, &origin))
        };
        self.outcomes
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push(outcome.clone());

        match outcome {
            ConnectOutcome::RefusedByCap { .. } => {
                // The held cap does not authorize this origin — no byte socket opens.
                return Box::pin(std::future::ready(Response::network_error(
                    NetworkError::LoadCancelled,
                )));
            }
            ConnectOutcome::RefusedByTransport { reason, .. } => {
                // Cap admitted it, but the audited netlayer could not reach the peer —
                // the transport's refusal, distinct from an ambient-socket fallback.
                return Box::pin(std::future::ready(Response::network_error(
                    NetworkError::ResourceLoadError(format!(
                        "net-cap transport could not reach {origin} ({reason})"
                    )),
                )));
            }
            ConnectOutcome::Dialed { .. } => { /* cap admitted + peer reachable — fetch the bytes */ }
        }

        // ── TOOTH 2: THE REAL BYTE SOCKET ────────────────────────────────────────
        // The cap admitted the origin. Open a REAL TCP socket to the origin and fetch
        // the bytes — plaintext for `http://`, a real rustls TLS handshake for
        // `https://` (same socket, same cap-gate-first). THIS socket is the embedder's,
        // opened only after the cap gate said yes.
        let fetched = if url.scheme() == "https" {
            let extra_roots = self
                .extra_roots
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .clone();
            let r = https_get_over_real_socket(&url, &extra_roots);
            if r.is_ok() {
                *self.last_tls_handshake.lock().unwrap_or_else(|e| e.into_inner()) = true;
            }
            r
        } else {
            http_get_over_real_socket(&url)
        };
        let timing = ResourceFetchTiming::new(request.timing_type());

        match fetched {
            Ok(HttpFetch { status, content_type, body }) => {
                *self.last_fetch.lock().unwrap_or_else(|e| e.into_inner()) =
                    Some((url.as_str().to_string(), body.len()));
                let mut response = Response::new(url, timing);
                *response.body.lock() = ResponseBody::Done(body);
                if let Ok(ct) = http::header::HeaderValue::from_str(&content_type) {
                    response.headers.insert(http::header::CONTENT_TYPE, ct);
                }
                // A real http status (200/…); default if the line was unparsable.
                response.status =
                    servo::protocol_handler::HttpStatus::new_raw(status, Vec::new());
                Box::pin(std::future::ready(response))
            }
            Err(e) => Box::pin(std::future::ready(Response::network_error(
                NetworkError::ResourceLoadError(format!("cap-gated http fetch failed: {e}")),
            ))),
        }
    }
}

/// A shared handle to a [`CapGatedHttpHandler`] that IS a `ProtocolHandler` —
/// a local newtype over `Arc<CapGatedHttpHandler>` so we can `impl ProtocolHandler`
/// (the orphan rule forbids impl-ing the foreign `ProtocolHandler` on the foreign
/// `Arc` directly). `ProtocolRegistry::register` takes the handler by value
/// (`impl ProtocolHandler + 'static`), so we register a clone of this handle and
/// retain another for audit readback — both share ONE handler (one audit trail).
#[derive(Clone)]
pub struct SharedHttpHandler(pub std::sync::Arc<CapGatedHttpHandler>);

impl SharedHttpHandler {
    /// The shared handler (for audit readback — outcomes, last fetch).
    pub fn handler(&self) -> &CapGatedHttpHandler {
        &self.0
    }
}

impl ProtocolHandler for SharedHttpHandler {
    fn is_fetchable(&self) -> bool {
        self.0.is_fetchable()
    }

    fn load<'a>(
        &'a self,
        request: &'a mut Request,
        done_chan: &mut DoneChannel,
        context: &FetchContext,
    ) -> Pin<Box<dyn Future<Output = Response> + Send + 'a>> {
        self.0.load(request, done_chan, context)
    }
}

/// A fetched http response, split into the pieces servo's `Response` needs.
struct HttpFetch {
    status: u16,
    content_type: String,
    body: Vec<u8>,
}

/// **THE REAL BYTE SOCKET (plaintext).** A minimal, genuine HTTP/1.1 `GET` over a real
/// `std::net::TcpStream` — no hyper, no servo net stack. Opens the socket to the
/// url's host:port, writes a real request line + headers, reads the whole response,
/// splits the status line / headers / body. Plain `http://` only. Returns the parsed
/// status, content-type, and body bytes.
fn http_get_over_real_socket(url: &ServoUrl) -> Result<HttpFetch, String> {
    if url.scheme() != "http" {
        return Err(format!(
            "the plaintext byte socket speaks http; '{}' is dispatched to the TLS leg",
            url.scheme()
        ));
    }
    let host = url.host_str().ok_or_else(|| "no host in url".to_string())?;
    let port = url.port_or_known_default().unwrap_or(80);
    let mut stream = connect_tcp(host, port)?;
    let req = http_request_bytes(host, request_path(url));
    stream
        .write_all(req.as_bytes())
        .map_err(|e| format!("write request: {e}"))?;
    stream.flush().map_err(|e| e.to_string())?;

    let mut raw = Vec::new();
    stream
        .read_to_end(&mut raw)
        .map_err(|e| format!("read response: {e}"))?;
    parse_http_response(&raw)
}

/// **THE REAL BYTE SOCKET (TLS).** The `https://` leg: open the SAME real
/// `std::net::TcpStream`, then drive a genuine `rustls` TLS handshake over it (keyed on
/// the SNI host) and do the HTTP/1.1 `GET` over the encrypted `StreamOwned`. The
/// verifier trusts the Mozilla CA set (`webpki-roots`) plus any embedder-supplied
/// `extra_roots` (a test's self-signed cert) — real cert validation, NOT a
/// danger-accept bypass. The cap gate has ALREADY admitted the origin before this is
/// reached (in `load`), so no socket opens for a cap-denied https origin.
fn https_get_over_real_socket(
    url: &ServoUrl,
    extra_roots: &[CertificateDer<'static>],
) -> Result<HttpFetch, String> {
    let host = url.host_str().ok_or_else(|| "no host in url".to_string())?;
    let port = url.port_or_known_default().unwrap_or(443);

    // The genuine rustls verifier: Mozilla CA roots + any embedder extras. The default
    // (no extras) verifies a public https origin against the real public roots.
    let mut root_store = RootCertStore::empty();
    root_store.extend(webpki_roots::TLS_SERVER_ROOTS.iter().cloned());
    for cert in extra_roots {
        // Ignore an unparsable extra root rather than poison the whole store.
        let _ = root_store.add(cert.clone());
    }
    let config = ClientConfig::builder()
        .with_root_certificates(root_store)
        .with_no_client_auth();

    // SNI / cert-name = the url host (an IP literal like 127.0.0.1 is a valid
    // `ServerName::IpAddress`; a hostname is `ServerName::DnsName`).
    let server_name: ServerName<'static> = ServerName::try_from(host.to_string())
        .map_err(|e| format!("invalid TLS server name '{host}': {e}"))?;
    let conn = ClientConnection::new(Arc::new(config), server_name)
        .map_err(|e| format!("rustls client setup for {host}: {e}"))?;

    let tcp = connect_tcp(host, port)?;
    // `StreamOwned` drives the handshake lazily on first IO (`complete_io`); the
    // `write_all` below forces it, so a handshake failure surfaces here as an error
    // (and no bytes/`last_tls_handshake=true` are produced).
    let mut tls = StreamOwned::new(conn, tcp);

    let req = http_request_bytes(host, request_path(url));
    tls.write_all(req.as_bytes())
        .map_err(|e| format!("TLS write request to {host}: {e}"))?;
    tls.flush().map_err(|e| format!("TLS flush to {host}: {e}"))?;

    let mut raw = Vec::new();
    match tls.read_to_end(&mut raw) {
        Ok(_) => {}
        // A `close_notify`-less server (common for `Connection: close`) makes rustls
        // surface `UnexpectedEof`; the body is already fully read, so treat it as EOF.
        Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof && !raw.is_empty() => {}
        Err(e) => return Err(format!("TLS read response from {host}: {e}")),
    }
    parse_http_response(&raw)
}

/// Open a real `std::net::TcpStream` to `host:port` with read/write timeouts. Shared by
/// the plaintext and TLS legs (the TLS handshake then runs OVER this same socket).
fn connect_tcp(host: &str, port: u16) -> Result<TcpStream, String> {
    let addr = format!("{host}:{port}");
    let stream = TcpStream::connect(&addr).map_err(|e| format!("connect {addr}: {e}"))?;
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .map_err(|e| e.to_string())?;
    stream
        .set_write_timeout(Some(Duration::from_secs(10)))
        .map_err(|e| e.to_string())?;
    Ok(stream)
}

/// The request path from a url (non-empty, default `/`).
fn request_path(url: &ServoUrl) -> String {
    let p = url.path();
    if p.is_empty() { "/".to_string() } else { p.to_string() }
}

/// A real HTTP/1.1 `GET` request. `Connection: close` so the server closes the socket
/// at end-of-body and our read-to-EOF terminates without chunked/keep-alive bookkeeping.
fn http_request_bytes(host: &str, path: String) -> String {
    format!(
        "GET {path} HTTP/1.1\r\n\
         Host: {host}\r\n\
         User-Agent: dregg-servo-render-netcap/0.1\r\n\
         Accept: text/html,*/*\r\n\
         Connection: close\r\n\r\n"
    )
}

/// Split a raw HTTP/1.1 response into status / content-type / body (shared by both legs).
fn parse_http_response(raw: &[u8]) -> Result<HttpFetch, String> {
    // Split head / body at the first CRLFCRLF.
    let sep = b"\r\n\r\n";
    let head_end = raw
        .windows(4)
        .position(|w| w == sep)
        .ok_or_else(|| "no header/body separator in response".to_string())?;
    let head = &raw[..head_end];
    let body = raw[head_end + 4..].to_vec();

    let head_str = String::from_utf8_lossy(head);
    let mut lines = head_str.split("\r\n");
    let status_line = lines.next().unwrap_or("");
    // "HTTP/1.1 200 OK" → 200
    let status = status_line
        .split_whitespace()
        .nth(1)
        .and_then(|c| c.parse::<u16>().ok())
        .unwrap_or(200);

    let mut content_type = "text/html; charset=utf-8".to_string();
    for line in lines {
        if let Some((name, value)) = line.split_once(':') {
            if name.trim().eq_ignore_ascii_case("content-type") {
                content_type = value.trim().to_string();
            }
        }
    }

    Ok(HttpFetch { status, content_type, body })
}
