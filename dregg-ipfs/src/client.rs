//! `client` — the **injected IPFS transport seam**.
//!
//! The verified core never talks to a network. [`IpfsClient`] is the seam (the same
//! shape the bridge uses for its `dregg_verify` RPCs): pin bytes → get a CID, fetch
//! by CID, pin a CID. Three impls cross the seam:
//!
//! - [`MockIpfs`] — an in-process content-addressed store. No network; the whole
//!   bridge round-trip (and the tamper-refusal) is exercised in `cargo test`. It can
//!   be told to [`MockIpfs::tamper`] a stored blob to play a lying node.
//! - [`KuboClient`] — the real Kubo HTTP RPC API (`/api/v0/add|block/get|pin/add`),
//!   formatted as plain requests and delegated to an **injected** [`HttpPost`]. The
//!   client itself pulls no HTTP/TLS crate; the caller supplies the transport
//!   (reqwest in the gateway, or the bundled [`StdHttpPost`] for a local daemon).
//! - [`StdHttpPost`] — a std-only plain-HTTP/1.1 POST to a local Kubo daemon
//!   (`127.0.0.1:5001`, no TLS), so a real, dependency-free transport exists. Live
//!   use against a running daemon is reviewed-go (ops); the type compiles offline.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Mutex;

use crate::cid::Cid;

/// Why an IPFS operation failed.
#[derive(Debug)]
pub enum IpfsError {
    /// The CID was not present in the store / not retrievable.
    NotFound(String),
    /// A fetched blob's recomputed CID disagrees with the requested CID — the node
    /// served the wrong bytes (the headline tamper tooth). Carries both CIDs.
    CidMismatch { requested: String, got: String },
    /// `fetch_verified` was asked to flat-verify a non-raw-blake3 CID (a chunked DAG
    /// root cannot be checked by a flat re-hash; see [`crate::fetch_verified`]).
    NotVerifiableByFlatHash(String),
    /// A single-block pin (`put_raw` / [`crate::pin_blob`]) was handed content larger
    /// than one IPFS block. The daemon would chunk it into a UnixFS DAG and return a
    /// dag-pb root — which is *not* `raw(blake3(bytes))`. Use [`crate::unixfs::pin_file`]
    /// for content this size instead of forcing it through the single-block path.
    BlockTooLarge { size: usize, max: usize },
    /// A single-block `put_raw` came back with a **dag-pb** root CID: the daemon
    /// chunked the content into a UnixFS DAG rather than pinning it as one raw block.
    /// Surfaced distinctly (not as a confusing [`CidMismatch`](IpfsError::CidMismatch))
    /// so the caller knows to read/write it through the DAG path.
    ChunkedDagRoot(String),
    /// A dag-pb / UnixFS node could not be parsed during the verified DAG walk.
    BadDagNode(String),
    /// A UnixFS **directory** shape was violated: a duplicate / empty entry name at
    /// build time, a directory read as a file (or vice versa), a nested directory
    /// (out of this bridge's single-level scope), or a directory node that would
    /// exceed one block. Named distinctly from [`BadDagNode`](IpfsError::BadDagNode)
    /// (a malformed node) — the node here is well-formed but the wrong shape.
    InvalidDirectory(String),
    /// The verified DAG walk exceeded its link-depth bound (a defense against a
    /// maliciously deep or cyclic DAG served by a lying node).
    DagTooDeep { max_depth: usize },
    /// The transport does not implement this operation (e.g. a POST-only [`HttpPost`]
    /// asked to perform an authenticated GET, or a client without block/put support).
    Unsupported(String),
    /// The owner-receipt check refused the read: the CID is not the one the owner
    /// committed for this content (the *whose-bytes* half; see
    /// [`crate::bridge::fetch_authorized`]).
    Unauthorized(String),
    /// The transport (HTTP / socket) failed.
    Transport(String),
    /// A non-2xx HTTP response, with the status code preserved so a caller can map it
    /// (e.g. 404 → [`NotFound`](IpfsError::NotFound)).
    Http { status: u16, body: String },
    /// The daemon's response could not be parsed (e.g. no `Hash` field on `add`).
    BadResponse(String),
}

impl fmt::Display for IpfsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IpfsError::NotFound(c) => write!(f, "CID not found: {c}"),
            IpfsError::CidMismatch { requested, got } => {
                write!(
                    f,
                    "fetched bytes hash to {got}, not the requested {requested}"
                )
            }
            IpfsError::NotVerifiableByFlatHash(c) => {
                write!(
                    f,
                    "CID {c} is not a raw blake3 blob (cannot flat-verify a DAG root)"
                )
            }
            IpfsError::BlockTooLarge { size, max } => write!(
                f,
                "content is {size} bytes, over the {max}-byte single-block limit (use unixfs::pin_file)"
            ),
            IpfsError::ChunkedDagRoot(c) => {
                write!(
                    f,
                    "daemon returned a chunked dag-pb root {c}, not a single raw block"
                )
            }
            IpfsError::BadDagNode(e) => write!(f, "malformed dag-pb/unixfs node: {e}"),
            IpfsError::InvalidDirectory(e) => write!(f, "invalid unixfs directory: {e}"),
            IpfsError::DagTooDeep { max_depth } => {
                write!(f, "DAG walk exceeded the max depth of {max_depth}")
            }
            IpfsError::Unsupported(e) => write!(f, "unsupported by this transport: {e}"),
            IpfsError::Unauthorized(e) => write!(f, "receipt refused: {e}"),
            IpfsError::Transport(e) => write!(f, "ipfs transport error: {e}"),
            IpfsError::Http { status, body } => write!(f, "HTTP {status}: {body}"),
            IpfsError::BadResponse(e) => write!(f, "ipfs bad response: {e}"),
        }
    }
}

impl std::error::Error for IpfsError {}

/// The injected IPFS transport. The bridge is written entirely against this trait,
/// so storage/hosting/merge pin + fetch the same way whether the transport is the
/// in-process [`MockIpfs`] or a real daemon.
pub trait IpfsClient {
    /// Pin `bytes` as a single **raw** block and return its CID. For a whole-blob
    /// pin the returned CID is `raw(blake3(bytes))` — the dregg content commitment.
    fn put_raw(&self, bytes: &[u8]) -> Result<Cid, IpfsError>;

    /// Store one already-CIDed block under `cid` — a raw leaf **or** a dag-pb node
    /// (the building blocks of a UnixFS DAG; see [`crate::unixfs`]). The default impl
    /// reports [`IpfsError::Unsupported`]; [`MockIpfs`] and [`KuboClient`] override it.
    /// Implementations MUST refuse a block whose `blake3` does not match `cid`'s
    /// digest (a caller cannot smuggle bytes under the wrong address).
    fn put_block(&self, cid: &Cid, bytes: &[u8]) -> Result<(), IpfsError> {
        let _ = (cid, bytes);
        Err(IpfsError::Unsupported("put_block".into()))
    }

    /// Fetch the block bytes addressed by `cid` (no verification — that is
    /// [`crate::fetch_verified`]'s job, which a caller should always prefer).
    fn get(&self, cid: &Cid) -> Result<Vec<u8>, IpfsError>;

    /// Pin an already-present `cid` (keep it from being garbage-collected).
    fn pin(&self, cid: &Cid) -> Result<(), IpfsError>;
}

// -- MockIpfs -----------------------------------------------------------------

/// An in-process content-addressed store standing in for an IPFS node. Keyed by CID
/// string; `put_raw` computes the raw blake3 CID and stores+pins the bytes.
#[derive(Default)]
pub struct MockIpfs {
    blocks: Mutex<HashMap<String, Vec<u8>>>,
    pinned: Mutex<HashSet<String>>,
}

impl MockIpfs {
    /// A fresh, empty mock node.
    pub fn new() -> MockIpfs {
        MockIpfs::default()
    }

    /// Whether `cid` is pinned on this node.
    pub fn is_pinned(&self, cid: &Cid) -> bool {
        self.pinned
            .lock()
            .expect("mock poisoned")
            .contains(&cid.to_string_cid())
    }

    /// Number of distinct blocks stored.
    pub fn block_count(&self) -> usize {
        self.blocks.lock().expect("mock poisoned").len()
    }

    /// Forget (drop) the block stored under `cid` — model an unavailable / GC'd block
    /// so a fetch of a DAG missing one child fails with [`IpfsError::NotFound`].
    pub fn forget(&self, cid: &Cid) {
        let key = cid.to_string_cid();
        self.blocks.lock().expect("mock poisoned").remove(&key);
        self.pinned.lock().expect("mock poisoned").remove(&key);
    }

    /// **Play a lying node:** overwrite the bytes stored under `cid` with `evil`
    /// WITHOUT changing the key, so a subsequent [`get`](IpfsClient::get) returns
    /// bytes that do not hash to `cid`. The honest content-address check
    /// ([`crate::fetch_verified`]) must then refuse the read.
    pub fn tamper(&self, cid: &Cid, evil: &[u8]) {
        self.blocks
            .lock()
            .expect("mock poisoned")
            .insert(cid.to_string_cid(), evil.to_vec());
    }
}

impl IpfsClient for MockIpfs {
    fn put_raw(&self, bytes: &[u8]) -> Result<Cid, IpfsError> {
        let cid = Cid::raw_blake3(bytes);
        let key = cid.to_string_cid();
        self.blocks
            .lock()
            .expect("mock poisoned")
            .insert(key.clone(), bytes.to_vec());
        self.pinned.lock().expect("mock poisoned").insert(key);
        Ok(cid)
    }

    fn put_block(&self, cid: &Cid, bytes: &[u8]) -> Result<(), IpfsError> {
        // The block's bytes must actually hash to the CID's blake3 digest (holds for
        // raw leaves and dag-pb nodes alike — both are blake3 over the block bytes).
        if cid.is_blake3() {
            let got = *blake3::hash(bytes).as_bytes();
            if got.as_slice() != cid.digest.as_slice() {
                return Err(IpfsError::CidMismatch {
                    requested: cid.to_string_cid(),
                    got: Cid::from_blake3_digest(cid.codec, got).to_string_cid(),
                });
            }
        } else {
            return Err(IpfsError::Unsupported(
                "put_block only stores blake3-addressed blocks".into(),
            ));
        }
        let key = cid.to_string_cid();
        self.blocks
            .lock()
            .expect("mock poisoned")
            .insert(key.clone(), bytes.to_vec());
        self.pinned.lock().expect("mock poisoned").insert(key);
        Ok(())
    }

    fn get(&self, cid: &Cid) -> Result<Vec<u8>, IpfsError> {
        self.blocks
            .lock()
            .expect("mock poisoned")
            .get(&cid.to_string_cid())
            .cloned()
            .ok_or_else(|| IpfsError::NotFound(cid.to_string_cid()))
    }

    fn pin(&self, cid: &Cid) -> Result<(), IpfsError> {
        let key = cid.to_string_cid();
        if !self
            .blocks
            .lock()
            .expect("mock poisoned")
            .contains_key(&key)
        {
            return Err(IpfsError::NotFound(key));
        }
        self.pinned.lock().expect("mock poisoned").insert(key);
        Ok(())
    }
}

// -- the injected HTTP transport for the real Kubo client ---------------------

/// One HTTP request across the transport seam: a method verb, a URL, request
/// headers (for auth / content negotiation), and an optional body. Constructed by the
/// higher-level clients ([`KuboClient`], [`GatewayClient`], [`PinningServiceClient`])
/// and handed to an injected [`HttpPost`].
#[derive(Clone, Debug)]
pub struct HttpRequest {
    /// The method verb (`GET`, `POST`, …).
    pub method: String,
    /// The absolute URL.
    pub url: String,
    /// Request headers as `(name, value)` pairs — carries `Authorization`, `Accept`
    /// (trustless-gateway `application/vnd.ipld.raw`), `Content-Type`, etc.
    pub headers: Vec<(String, String)>,
    /// The request body (empty for a GET).
    pub body: Vec<u8>,
}

impl HttpRequest {
    /// A GET with no body.
    pub fn get(url: impl Into<String>) -> HttpRequest {
        HttpRequest {
            method: "GET".into(),
            url: url.into(),
            headers: Vec::new(),
            body: Vec::new(),
        }
    }

    /// A POST with a body and content type.
    pub fn post(url: impl Into<String>, content_type: &str, body: Vec<u8>) -> HttpRequest {
        HttpRequest {
            method: "POST".into(),
            url: url.into(),
            headers: vec![("Content-Type".into(), content_type.into())],
            body,
        }
    }

    /// Append a header (builder style).
    pub fn with_header(mut self, name: impl Into<String>, value: impl Into<String>) -> HttpRequest {
        self.headers.push((name.into(), value.into()));
        self
    }
}

/// An HTTP response across the seam: the status code plus the body bytes.
#[derive(Clone, Debug)]
pub struct HttpResponse {
    /// The HTTP status code.
    pub status: u16,
    /// The response body.
    pub body: Vec<u8>,
}

/// The injected HTTP transport the real clients format requests over. Injecting this
/// keeps `dregg-ipfs` free of any HTTP/TLS crate — the gateway supplies a
/// reqwest-backed impl, a local tool the bundled [`StdHttpPost`].
///
/// The required method is [`post`](HttpPost::post) (POST + body, 2xx-or-error), which
/// is all [`KuboClient`] needs. [`request`](HttpPost::request) is the richer surface
/// (method verb + headers + status), needed for authenticated GETs (a trustless
/// gateway, a pinning service); its default routes a plain POST through `post` and
/// otherwise reports [`IpfsError::Unsupported`], so a transport that only implements
/// `post` still works for Kubo. [`StdHttpPost`] implements `request` fully.
pub trait HttpPost {
    /// POST `body` (with `content_type`) to `url`; return the response body bytes on a
    /// 2xx, else an error.
    fn post(&self, url: &str, content_type: &str, body: Vec<u8>) -> Result<Vec<u8>, IpfsError>;

    /// Perform an arbitrary request (method + headers), returning the status and body
    /// (a non-2xx is *not* an error here — the caller decides, e.g. 404 → NotFound).
    fn request(&self, req: HttpRequest) -> Result<HttpResponse, IpfsError> {
        // Default: only a header-free POST can be expressed over `post`.
        if req.method == "POST" {
            let ct = req
                .headers
                .iter()
                .find(|(k, _)| k.eq_ignore_ascii_case("content-type"))
                .map(|(_, v)| v.as_str())
                .unwrap_or("application/octet-stream");
            let extra = req
                .headers
                .iter()
                .any(|(k, _)| !k.eq_ignore_ascii_case("content-type"));
            if !extra {
                let body = self.post(&req.url, ct, req.body)?;
                return Ok(HttpResponse { status: 200, body });
            }
        }
        Err(IpfsError::Unsupported(format!(
            "this HttpPost transport cannot perform a {} with custom headers; \
             supply a transport that implements HttpPost::request",
            req.method
        )))
    }
}

/// The real **Kubo HTTP RPC** client — a pure formatter over an injected
/// [`HttpPost`]. It builds the `/api/v0/*` requests and parses the responses; the
/// caller owns the actual HTTP.
pub struct KuboClient<H: HttpPost> {
    /// The API base, e.g. `http://127.0.0.1:5001`.
    base: String,
    http: H,
}

impl<H: HttpPost> KuboClient<H> {
    /// A client against `base` (`http://127.0.0.1:5001` for a local daemon) using
    /// `http` as the transport.
    pub fn new(base: impl Into<String>, http: H) -> KuboClient<H> {
        KuboClient {
            base: base.into(),
            http,
        }
    }

    /// The default local daemon endpoint.
    pub fn local(http: H) -> KuboClient<H> {
        KuboClient::new("http://127.0.0.1:5001", http)
    }
}

/// A multipart/form-data body with one `file` part — the shape `ipfs add` expects.
fn multipart_file(bytes: &[u8]) -> (String, Vec<u8>) {
    let boundary = "------------------------dreggipfsboundary";
    let mut body = Vec::new();
    body.extend_from_slice(format!("--{boundary}\r\n").as_bytes());
    body.extend_from_slice(b"Content-Disposition: form-data; name=\"file\"; filename=\"blob\"\r\n");
    body.extend_from_slice(b"Content-Type: application/octet-stream\r\n\r\n");
    body.extend_from_slice(bytes);
    body.extend_from_slice(format!("\r\n--{boundary}--\r\n").as_bytes());
    (format!("multipart/form-data; boundary={boundary}"), body)
}

impl<H: HttpPost> IpfsClient for KuboClient<H> {
    fn put_raw(&self, bytes: &[u8]) -> Result<Cid, IpfsError> {
        // `cid-version=1 hash=blake3 raw-leaves=true` makes the returned CID a
        // raw blake3 CIDv1 — i.e. the dregg content commitment. `pin=true` keeps it.
        let url = format!(
            "{}/api/v0/add?cid-version=1&hash=blake3&raw-leaves=true&pin=true",
            self.base
        );
        let (content_type, body) = multipart_file(bytes);
        let resp = self.http.post(&url, &content_type, body)?;
        let hash = parse_add_hash(&resp)?;
        let cid = Cid::parse(&hash)
            .map_err(|e| IpfsError::BadResponse(format!("bad CID `{hash}`: {e}")))?;
        // If the daemon chunked `bytes` into a UnixFS DAG (content over one block) it
        // returns a dag-pb root, NOT `raw(blake3(bytes))`. Surface that distinctly so
        // the caller does not see a baffling CidMismatch from `pin_blob`.
        if cid.is_dag_pb() {
            return Err(IpfsError::ChunkedDagRoot(cid.to_string_cid()));
        }
        Ok(cid)
    }

    fn put_block(&self, cid: &Cid, bytes: &[u8]) -> Result<(), IpfsError> {
        // `block/put` stores one already-CIDed block. `mhtype=blake3` + the block's
        // own codec reproduce the exact CID; we assert the daemon agreed.
        let codec = if cid.codec == crate::cid::CODEC_DAG_PB {
            "dag-pb"
        } else {
            "raw"
        };
        let url = format!(
            "{}/api/v0/block/put?cid-codec={codec}&mhtype=blake3&mhlen=32&pin=true",
            self.base
        );
        let (content_type, body) = multipart_file(bytes);
        let resp = self.http.post(&url, &content_type, body)?;
        let key = parse_block_put_key(&resp)?;
        let got = Cid::parse(&key)
            .map_err(|e| IpfsError::BadResponse(format!("bad block/put key `{key}`: {e}")))?;
        if &got != cid {
            return Err(IpfsError::CidMismatch {
                requested: cid.to_string_cid(),
                got: got.to_string_cid(),
            });
        }
        Ok(())
    }

    fn get(&self, cid: &Cid) -> Result<Vec<u8>, IpfsError> {
        // `block/get` returns exactly the raw block bytes for a whole-blob pin.
        let url = format!("{}/api/v0/block/get?arg={}", self.base, cid.to_string_cid());
        let req = HttpRequest::post(url, "application/octet-stream", Vec::new());
        let resp = self.http.request(req)?;
        classify_get_status(resp, cid)
    }

    fn pin(&self, cid: &Cid) -> Result<(), IpfsError> {
        let url = format!("{}/api/v0/pin/add?arg={}", self.base, cid.to_string_cid());
        self.http
            .post(&url, "application/octet-stream", Vec::new())?;
        Ok(())
    }
}

/// Map a Kubo `block/get` HTTP response to bytes, translating a missing-block signal
/// into [`IpfsError::NotFound`] (Kubo answers a missing CID with a 500 whose body says
/// "not found"/"could not find"; a trustless gateway answers 404). Any other non-2xx
/// stays an [`IpfsError::Http`].
fn classify_get_status(resp: HttpResponse, cid: &Cid) -> Result<Vec<u8>, IpfsError> {
    if (200..300).contains(&resp.status) {
        return Ok(resp.body);
    }
    let body = String::from_utf8_lossy(&resp.body);
    let lower = body.to_ascii_lowercase();
    if resp.status == 404 || lower.contains("not found") || lower.contains("could not find") {
        return Err(IpfsError::NotFound(cid.to_string_cid()));
    }
    Err(IpfsError::Http {
        status: resp.status,
        body: body.chars().take(200).collect(),
    })
}

/// Pull the CID out of a `block/put` JSON response (`{"Key":"bafk…","Size":N}`).
fn parse_block_put_key(resp: &[u8]) -> Result<String, IpfsError> {
    let text = std::str::from_utf8(resp)
        .map_err(|_| IpfsError::BadResponse("non-utf8 block/put response".into()))?;
    let line = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .next_back()
        .unwrap_or("");
    let v: serde_json::Value = serde_json::from_str(line)
        .map_err(|e| IpfsError::BadResponse(format!("block/put response not JSON: {e}")))?;
    v.get("Key")
        .and_then(|h| h.as_str())
        .map(|s| s.to_string())
        .ok_or_else(|| IpfsError::BadResponse("block/put response had no `Key`".into()))
}

/// Pull the `"Hash"` field out of an `ipfs add` JSON response line.
fn parse_add_hash(resp: &[u8]) -> Result<String, IpfsError> {
    // `add` streams one JSON object per added entry; for a single file there is one
    // line. Parse the (last) JSON object and read `Hash`.
    let text = std::str::from_utf8(resp)
        .map_err(|_| IpfsError::BadResponse("non-utf8 add response".into()))?;
    let line = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .next_back()
        .unwrap_or("");
    let v: serde_json::Value = serde_json::from_str(line)
        .map_err(|e| IpfsError::BadResponse(format!("add response not JSON: {e}")))?;
    v.get("Hash")
        .and_then(|h| h.as_str())
        .map(|s| s.to_string())
        .ok_or_else(|| IpfsError::BadResponse("add response had no `Hash`".into()))
}

// -- StdHttpPost: a std-only plain-HTTP transport for a local daemon ----------

/// A dependency-free [`HttpPost`] over `std::net::TcpStream`, plain HTTP/1.1 — for a
/// **local** Kubo daemon (the RPC is unauthenticated plain HTTP on `127.0.0.1:5001`,
/// no TLS). It compiles everywhere; live use against a running daemon is reviewed-go.
///
/// Connect/read/write are bounded by [`timeout`](StdHttpPost::timeout) so a hung
/// daemon fails fast instead of blocking forever. **`https://` is refused** — TLS is
/// out of scope for the std transport; an authenticated Kubo, a remote gateway, or a
/// pinning service supplies a TLS-capable [`HttpPost`] (reqwest) across the same seam.
#[derive(Clone, Debug)]
pub struct StdHttpPost {
    /// The connect + per-read/write timeout. Applied to every socket operation.
    timeout: std::time::Duration,
}

impl Default for StdHttpPost {
    fn default() -> StdHttpPost {
        StdHttpPost {
            timeout: std::time::Duration::from_secs(30),
        }
    }
}

impl StdHttpPost {
    /// A new std transport with the default 30s timeout.
    pub fn new() -> StdHttpPost {
        StdHttpPost::default()
    }

    /// A std transport with an explicit connect/read/write timeout.
    pub fn with_timeout(timeout: std::time::Duration) -> StdHttpPost {
        StdHttpPost { timeout }
    }
}

impl HttpPost for StdHttpPost {
    fn post(&self, url: &str, content_type: &str, body: Vec<u8>) -> Result<Vec<u8>, IpfsError> {
        let resp = self.request(HttpRequest::post(url, content_type, body))?;
        if (200..300).contains(&resp.status) {
            Ok(resp.body)
        } else {
            Err(IpfsError::Http {
                status: resp.status,
                body: String::from_utf8_lossy(&resp.body)
                    .chars()
                    .take(200)
                    .collect(),
            })
        }
    }

    fn request(&self, req: HttpRequest) -> Result<HttpResponse, IpfsError> {
        use std::io::{Read, Write};
        use std::net::{TcpStream, ToSocketAddrs};

        let (host_port, path) = split_url(&req.url)?;
        // Resolve + connect with a bounded timeout so a black-holed daemon fails fast.
        let addr = host_port
            .to_socket_addrs()
            .map_err(|e| IpfsError::Transport(format!("resolve {host_port}: {e}")))?
            .next()
            .ok_or_else(|| IpfsError::Transport(format!("no address for {host_port}")))?;
        let mut stream = TcpStream::connect_timeout(&addr, self.timeout)
            .map_err(|e| IpfsError::Transport(format!("connect {host_port}: {e}")))?;
        stream
            .set_read_timeout(Some(self.timeout))
            .and_then(|_| stream.set_write_timeout(Some(self.timeout)))
            .map_err(|e| IpfsError::Transport(format!("set timeout: {e}")))?;

        // Assemble the request. Content-Length + Host are always set; caller headers
        // (Authorization, Accept, Content-Type, …) are appended verbatim.
        let mut head = format!(
            "{} {path} HTTP/1.1\r\nHost: {host_port}\r\nContent-Length: {}\r\nConnection: close\r\n",
            req.method,
            req.body.len()
        );
        for (k, v) in &req.headers {
            // Guard against header injection via a malformed key/value.
            if k.contains(['\r', '\n', ':']) || v.contains(['\r', '\n']) {
                return Err(IpfsError::Transport(format!("illegal header `{k}`")));
            }
            head.push_str(&format!("{k}: {v}\r\n"));
        }
        head.push_str("\r\n");

        stream
            .write_all(head.as_bytes())
            .and_then(|_| stream.write_all(&req.body))
            .map_err(|e| IpfsError::Transport(format!("write: {e}")))?;
        let mut raw = Vec::new();
        stream
            .read_to_end(&mut raw)
            .map_err(|e| IpfsError::Transport(format!("read: {e}")))?;
        decode_http_response(&raw)
    }
}

/// Split `http://host:port/path?query` into (`host:port`, `/path?query`). Only the
/// plain-HTTP scheme is supported (the local daemon).
fn split_url(url: &str) -> Result<(String, String), IpfsError> {
    let rest = url
        .strip_prefix("http://")
        .ok_or_else(|| IpfsError::Transport(format!("only http:// supported, got `{url}`")))?;
    match rest.find('/') {
        Some(i) => Ok((rest[..i].to_string(), rest[i..].to_string())),
        None => Ok((rest.to_string(), "/".to_string())),
    }
}

/// Parse an HTTP/1.1 response into an [`HttpResponse`] (status + body), decoding
/// `Content-Length` or `Transfer-Encoding: chunked`. A non-2xx is **not** an error
/// here — the status is preserved so the caller can classify it (404 → NotFound, …).
fn decode_http_response(raw: &[u8]) -> Result<HttpResponse, IpfsError> {
    let sep = find_subslice(raw, b"\r\n\r\n")
        .ok_or_else(|| IpfsError::Transport("no header/body separator".into()))?;
    let head = std::str::from_utf8(&raw[..sep])
        .map_err(|_| IpfsError::Transport("non-utf8 headers".into()))?;
    let body_raw = &raw[sep + 4..];

    let mut lines = head.lines();
    let status_line = lines.next().unwrap_or("");
    let status = status_line
        .split_whitespace()
        .nth(1)
        .and_then(|s| s.parse::<u16>().ok())
        .ok_or_else(|| IpfsError::Transport(format!("bad status line `{status_line}`")))?;

    let mut chunked = false;
    for line in lines {
        let lower = line.to_ascii_lowercase();
        if lower.starts_with("transfer-encoding:") && lower.contains("chunked") {
            chunked = true;
        }
    }
    let body = if chunked {
        dechunk(body_raw)?
    } else {
        body_raw.to_vec()
    };
    Ok(HttpResponse { status, body })
}

/// Decode an HTTP/1.1 chunked body.
fn dechunk(mut data: &[u8]) -> Result<Vec<u8>, IpfsError> {
    let mut out = Vec::new();
    loop {
        let nl = find_subslice(data, b"\r\n")
            .ok_or_else(|| IpfsError::Transport("truncated chunk size".into()))?;
        let size_str = std::str::from_utf8(&data[..nl])
            .map_err(|_| IpfsError::Transport("non-utf8 chunk size".into()))?
            .split(';')
            .next()
            .unwrap_or("")
            .trim();
        let size = usize::from_str_radix(size_str, 16)
            .map_err(|_| IpfsError::Transport(format!("bad chunk size `{size_str}`")))?;
        data = &data[nl + 2..];
        if size == 0 {
            break;
        }
        if data.len() < size {
            return Err(IpfsError::Transport("truncated chunk body".into()));
        }
        out.extend_from_slice(&data[..size]);
        data = &data[size..];
        // Skip the trailing CRLF after the chunk data.
        if data.len() >= 2 {
            data = &data[2..];
        }
    }
    Ok(out)
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|w| w == needle)
}

// -- GatewayClient: a trustless HTTP-gateway READ -----------------------------

/// A **trustless-gateway** read client (the [IPIP-402] `?format=raw` block read).
///
/// This is the "fetch from *any* gateway and re-witness" half as code, not prose: it
/// issues `GET {base}/ipfs/{cid}?format=raw` with `Accept: application/vnd.ipld.raw`,
/// which a trustless gateway answers with **exactly the one block** addressed by the
/// CID — no server-side reassembly to trust. Because it implements [`IpfsClient`], the
/// bridge's verified reads compose directly on top: [`crate::fetch_verified`] over a
/// raw blob, or [`crate::unixfs::fetch_cat`] to walk a whole DAG block-by-block, each
/// block re-hashed against its own CID. A byte the gateway flips moves the hash and is
/// refused — the trust root is the CID, never the gateway.
///
/// Read-only: `put_raw`/`put_block`/`pin` are [`IpfsError::Unsupported`] (a gateway
/// serves, it does not accept writes — pin via [`KuboClient`] or a
/// [`PinningServiceClient`]). An optional bearer token is sent for gateways behind
/// auth. Requires a transport implementing [`HttpPost::request`] (the default POST-only
/// fallback cannot issue the authenticated GET).
///
/// [IPIP-402]: https://specs.ipfs.tech/http-gateways/trustless-gateway/
pub struct GatewayClient<H: HttpPost> {
    base: String,
    auth: Option<String>,
    http: H,
}

impl<H: HttpPost> GatewayClient<H> {
    /// A gateway client against `base` (e.g. `https://ipfs.io` or a private gateway).
    pub fn new(base: impl Into<String>, http: H) -> GatewayClient<H> {
        GatewayClient {
            base: base.into(),
            auth: None,
            http,
        }
    }

    /// Attach a bearer token sent as `Authorization: Bearer <token>` on every read
    /// (for a gateway behind authentication).
    pub fn with_bearer(mut self, token: impl Into<String>) -> GatewayClient<H> {
        self.auth = Some(token.into());
        self
    }

    fn raw_block_request(&self, cid: &Cid) -> HttpRequest {
        let url = format!("{}/ipfs/{}?format=raw", self.base, cid.to_string_cid());
        let mut req = HttpRequest::get(url).with_header("Accept", "application/vnd.ipld.raw");
        if let Some(tok) = &self.auth {
            req = req.with_header("Authorization", format!("Bearer {tok}"));
        }
        req
    }
}

impl<H: HttpPost> IpfsClient for GatewayClient<H> {
    fn put_raw(&self, _bytes: &[u8]) -> Result<Cid, IpfsError> {
        Err(IpfsError::Unsupported(
            "a read-only gateway cannot accept a pin".into(),
        ))
    }

    fn get(&self, cid: &Cid) -> Result<Vec<u8>, IpfsError> {
        let resp = self.http.request(self.raw_block_request(cid))?;
        classify_get_status(resp, cid)
    }

    fn pin(&self, _cid: &Cid) -> Result<(), IpfsError> {
        Err(IpfsError::Unsupported(
            "a read-only gateway cannot pin".into(),
        ))
    }
}

// -- PinningServiceClient: durability via the IPFS Pinning Service API ---------

/// The status of a pin request from an [IPFS Pinning Service API] provider.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PinStatus {
    /// The provider's request id (`requestid`) — the handle for polling/removal.
    pub request_id: String,
    /// The pin lifecycle status: `queued` | `pinning` | `pinned` | `failed`.
    pub status: String,
    /// The pinned CID as the provider echoed it.
    pub cid: String,
}

/// A client for the **[IPFS Pinning Service API]** — the durability layer behind
/// "retrievable from any gateway". A local `pin/add` ([`KuboClient::pin`]) only keeps
/// a block on *one* node; a pinning service (Pinata, web3.storage, a self-hosted
/// `ipfs-cluster` with the pinning API, …) commits a provider to *keep the content
/// available and reprovided to the DHT*, which is the actual mechanism that makes a
/// committed CID fetchable from an arbitrary gateway later.
///
/// A pure formatter over the injected [`HttpPost::request`] (bearer-auth'd JSON): the
/// caller owns the TLS transport. Live use against a provider is reviewed-go.
///
/// [IPFS Pinning Service API]: https://ipfs.github.io/pinning-services-api-spec/
pub struct PinningServiceClient<H: HttpPost> {
    base: String,
    token: String,
    http: H,
}

impl<H: HttpPost> PinningServiceClient<H> {
    /// A client against `base` (the provider's pinning API root, e.g.
    /// `https://api.pinata.cloud/psa`) authenticating with bearer `token`.
    pub fn new(
        base: impl Into<String>,
        token: impl Into<String>,
        http: H,
    ) -> PinningServiceClient<H> {
        PinningServiceClient {
            base: base.into(),
            token: token.into(),
            http,
        }
    }

    /// Request that the provider pin `cid` (optionally under `name`). `POST {base}/pins`
    /// with a bearer token; returns the provider's [`PinStatus`].
    pub fn add(&self, cid: &Cid, name: Option<&str>) -> Result<PinStatus, IpfsError> {
        let body = serde_json::json!({
            "cid": cid.to_string_cid(),
            "name": name.unwrap_or(""),
        });
        let req = HttpRequest::post(
            format!("{}/pins", self.base),
            "application/json",
            serde_json::to_vec(&body).expect("json"),
        )
        .with_header("Authorization", format!("Bearer {}", self.token));
        let resp = self.http.request(req)?;
        if !(200..300).contains(&resp.status) {
            return Err(IpfsError::Http {
                status: resp.status,
                body: String::from_utf8_lossy(&resp.body)
                    .chars()
                    .take(200)
                    .collect(),
            });
        }
        parse_pin_status(&resp.body)
    }

    /// Poll the status of a prior pin request. `GET {base}/pins/{request_id}`.
    pub fn status(&self, request_id: &str) -> Result<PinStatus, IpfsError> {
        let req = HttpRequest::get(format!("{}/pins/{request_id}", self.base))
            .with_header("Authorization", format!("Bearer {}", self.token));
        let resp = self.http.request(req)?;
        if resp.status == 404 {
            return Err(IpfsError::NotFound(request_id.to_string()));
        }
        if !(200..300).contains(&resp.status) {
            return Err(IpfsError::Http {
                status: resp.status,
                body: String::from_utf8_lossy(&resp.body)
                    .chars()
                    .take(200)
                    .collect(),
            });
        }
        parse_pin_status(&resp.body)
    }
}

/// Parse a Pinning-Service-API `PinStatus` JSON object (`requestid`, `status`, and the
/// echoed `pin.cid`).
fn parse_pin_status(body: &[u8]) -> Result<PinStatus, IpfsError> {
    let v: serde_json::Value = serde_json::from_slice(body)
        .map_err(|e| IpfsError::BadResponse(format!("pin status not JSON: {e}")))?;
    let request_id = v
        .get("requestid")
        .and_then(|x| x.as_str())
        .ok_or_else(|| IpfsError::BadResponse("pin status had no `requestid`".into()))?
        .to_string();
    let status = v
        .get("status")
        .and_then(|x| x.as_str())
        .unwrap_or("unknown")
        .to_string();
    let cid = v
        .get("pin")
        .and_then(|p| p.get("cid"))
        .and_then(|c| c.as_str())
        .unwrap_or("")
        .to_string();
    Ok(PinStatus {
        request_id,
        status,
        cid,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mock_put_pin_get_round_trip() {
        let node = MockIpfs::new();
        let bytes = b"the bytes the owner pinned";
        let cid = node.put_raw(bytes).unwrap();
        // put_raw pins it, and the CID is the raw blake3 commitment.
        assert!(node.is_pinned(&cid));
        assert_eq!(cid, Cid::raw_blake3(bytes));
        // Fetch by CID returns the exact bytes.
        assert_eq!(node.get(&cid).unwrap(), bytes);
        // Re-pinning an absent CID is NotFound.
        assert!(matches!(
            node.pin(&Cid::raw_blake3(b"never stored")),
            Err(IpfsError::NotFound(_))
        ));
    }

    #[test]
    fn mock_tamper_changes_the_served_bytes_under_the_same_key() {
        let node = MockIpfs::new();
        let cid = node.put_raw(b"honest").unwrap();
        node.tamper(&cid, b"EVIL");
        // The node now serves EVIL under the honest CID — the raw get does NOT catch
        // it (that is fetch_verified's job, tested in the bridge).
        assert_eq!(node.get(&cid).unwrap(), b"EVIL");
    }

    #[test]
    fn add_hash_parsing() {
        let resp = br#"{"Name":"blob","Hash":"bafkreibdummy","Size":"5"}"#;
        assert_eq!(parse_add_hash(resp).unwrap(), "bafkreibdummy");
        assert!(parse_add_hash(b"not json").is_err());
        assert!(parse_add_hash(br#"{"Name":"x"}"#).is_err());
    }

    #[test]
    fn dechunk_decodes() {
        // "Wikipedia in\r\n\r\nchunks." per the RFC example, lowercased sizes.
        let chunked = b"4\r\nWiki\r\n5\r\npedia\r\n0\r\n\r\n";
        assert_eq!(dechunk(chunked).unwrap(), b"Wikipedia");
    }

    #[test]
    fn http_response_decoding() {
        let ok = b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\r\n{\"Hash\":\"b\"}";
        let r = decode_http_response(ok).unwrap();
        assert_eq!(r.status, 200);
        assert_eq!(r.body, br#"{"Hash":"b"}"#);
        // A non-2xx is preserved (status + body), NOT flattened to a Transport error,
        // so a caller can map it (404 → NotFound).
        let err = decode_http_response(b"HTTP/1.1 500 Internal Server Error\r\n\r\nboom").unwrap();
        assert_eq!(err.status, 500);
        assert_eq!(err.body, b"boom");
    }

    #[test]
    fn classify_get_maps_missing_to_not_found() {
        let cid = Cid::raw_blake3(b"absent");
        // A 404 from a gateway → NotFound.
        assert!(matches!(
            classify_get_status(
                HttpResponse {
                    status: 404,
                    body: b"nope".to_vec()
                },
                &cid
            ),
            Err(IpfsError::NotFound(_))
        ));
        // Kubo answers a missing block with a 500 whose body says "not found".
        assert!(matches!(
            classify_get_status(
                HttpResponse {
                    status: 500,
                    body: b"block was not found locally".to_vec()
                },
                &cid
            ),
            Err(IpfsError::NotFound(_))
        ));
        // An unrelated 500 stays an Http error.
        assert!(matches!(
            classify_get_status(
                HttpResponse {
                    status: 503,
                    body: b"overloaded".to_vec()
                },
                &cid
            ),
            Err(IpfsError::Http { status: 503, .. })
        ));
        assert_eq!(
            classify_get_status(
                HttpResponse {
                    status: 200,
                    body: b"ok".to_vec()
                },
                &cid
            )
            .unwrap(),
            b"ok"
        );
    }

    #[test]
    fn url_splitting() {
        assert_eq!(
            split_url("http://127.0.0.1:5001/api/v0/add?pin=true").unwrap(),
            (
                "127.0.0.1:5001".to_string(),
                "/api/v0/add?pin=true".to_string()
            )
        );
        assert!(split_url("https://x/y").is_err());
    }

    /// A recording transport: captures every URL, replays a canned reply per URL
    /// substring. Lets us assert the real Kubo/gateway RPC *formatting* offline.
    #[derive(Default)]
    struct Recorder {
        urls: std::cell::RefCell<Vec<String>>,
        /// `(url-substring, reply-bytes)` — first match wins.
        replies: Vec<(String, Vec<u8>)>,
    }
    impl Recorder {
        fn last(&self) -> String {
            self.urls.borrow().last().cloned().unwrap_or_default()
        }
    }
    impl HttpPost for Recorder {
        fn post(&self, url: &str, _ct: &str, _body: Vec<u8>) -> Result<Vec<u8>, IpfsError> {
            self.urls.borrow_mut().push(url.to_string());
            for (needle, reply) in &self.replies {
                if url.contains(needle.as_str()) {
                    return Ok(reply.clone());
                }
            }
            Ok(Vec::new())
        }
    }

    /// The real Kubo client compiles + formats correctly over a recording transport
    /// (no live daemon). A live round-trip is reviewed-go.
    #[test]
    fn kubo_client_formats_rpc_calls() {
        let cid = Cid::raw_blake3(b"payload");
        let rec = Recorder {
            replies: vec![(
                "add".into(),
                format!(r#"{{"Name":"blob","Hash":"{cid}","Size":"7"}}"#).into_bytes(),
            )],
            ..Default::default()
        };
        let client = KuboClient::local(rec);

        // put_raw → /api/v0/add with the alignment flags.
        let got = client.put_raw(b"payload").unwrap();
        assert_eq!(got, cid, "add parses the returned CID");
        let add_url = client.http.last();
        assert!(add_url.contains("/api/v0/add"), "{add_url}");
        assert!(add_url.contains("hash=blake3"));
        assert!(add_url.contains("cid-version=1"));
        assert!(add_url.contains("raw-leaves=true"));

        // get → /api/v0/block/get?arg=<cid> (unhappy-path URL formatting, previously
        // never asserted).
        client.get(&cid).unwrap();
        let get_url = client.http.last();
        assert!(get_url.contains("/api/v0/block/get"), "{get_url}");
        assert!(get_url.contains(&format!("arg={cid}")), "{get_url}");

        // pin → /api/v0/pin/add?arg=<cid>.
        client.pin(&cid).unwrap();
        let pin_url = client.http.last();
        assert!(pin_url.contains("/api/v0/pin/add"), "{pin_url}");
        assert!(pin_url.contains(&format!("arg={cid}")), "{pin_url}");
    }

    /// `put_raw` distinguishes a chunked dag-pb return from a content-address
    /// disagreement: a daemon that chunked the content returns a dag-pb root, which is
    /// surfaced as `ChunkedDagRoot`, not a baffling `CidMismatch`.
    #[test]
    fn kubo_put_raw_detects_a_dag_pb_return() {
        // A dag-pb CID string the daemon might return for a chunked add.
        let dag = Cid::from_blake3_digest(crate::cid::CODEC_DAG_PB, [9u8; 32]);
        let rec = Recorder {
            replies: vec![(
                "add".into(),
                format!(r#"{{"Name":"blob","Hash":"{dag}","Size":"999999"}}"#).into_bytes(),
            )],
            ..Default::default()
        };
        let client = KuboClient::local(rec);
        assert!(
            matches!(
                client.put_raw(b"big").unwrap_err(),
                IpfsError::ChunkedDagRoot(_)
            ),
            "a dag-pb add return must be surfaced distinctly"
        );
    }

    /// `put_block` asserts the daemon reproduced the exact CID (`Key`).
    #[test]
    fn kubo_put_block_checks_the_returned_key() {
        let block = b"a dag node's bytes";
        let cid =
            Cid::from_blake3_digest(crate::cid::CODEC_DAG_PB, *blake3::hash(block).as_bytes());
        let rec = Recorder {
            replies: vec![(
                "block/put".into(),
                format!(r#"{{"Key":"{cid}","Size":"18"}}"#).into_bytes(),
            )],
            ..Default::default()
        };
        let client = KuboClient::local(rec);
        client.put_block(&cid, block).unwrap();
        assert!(client.http.last().contains("cid-codec=dag-pb"));
        assert!(client.http.last().contains("mhtype=blake3"));

        // A daemon returning the WRONG key is refused.
        let wrong = Cid::from_blake3_digest(crate::cid::CODEC_DAG_PB, [0u8; 32]);
        let rec2 = Recorder {
            replies: vec![(
                "block/put".into(),
                format!(r#"{{"Key":"{wrong}"}}"#).into_bytes(),
            )],
            ..Default::default()
        };
        let client2 = KuboClient::local(rec2);
        assert!(matches!(
            client2.put_block(&cid, block).unwrap_err(),
            IpfsError::CidMismatch { .. }
        ));
    }

    #[test]
    fn request_default_rejects_headers_a_plain_post_cannot_carry() {
        // The default HttpPost::request can express a header-free POST (routed through
        // `post`) but not an authenticated GET — that needs a real `request` impl.
        let rec = Recorder::default();
        let authed = HttpRequest::get("http://x/pins").with_header("Authorization", "Bearer t");
        assert!(matches!(
            rec.request(authed).unwrap_err(),
            IpfsError::Unsupported(_)
        ));
    }

    /// A transport that fully implements `request` (records the request, replays a
    /// canned response) — needed to test the gateway + pinning clients (auth'd GETs).
    #[derive(Default)]
    struct ReqRecorder {
        last: std::cell::RefCell<Option<HttpRequest>>,
        status: u16,
        body: Vec<u8>,
    }
    impl HttpPost for ReqRecorder {
        fn post(&self, _url: &str, _ct: &str, _body: Vec<u8>) -> Result<Vec<u8>, IpfsError> {
            unreachable!("gateway/pinning go through request")
        }
        fn request(&self, req: HttpRequest) -> Result<HttpResponse, IpfsError> {
            *self.last.borrow_mut() = Some(req);
            Ok(HttpResponse {
                status: self.status,
                body: self.body.clone(),
            })
        }
    }

    #[test]
    fn gateway_client_formats_a_trustless_raw_read() {
        let cid = Cid::raw_blake3(b"served by the gateway");
        let rec = ReqRecorder {
            status: 200,
            body: b"served by the gateway".to_vec(),
            ..Default::default()
        };
        let gw = GatewayClient::new("https://ipfs.example", rec).with_bearer("secret");
        let bytes = gw.get(&cid).unwrap();
        assert_eq!(bytes, b"served by the gateway");
        let req = gw.http.last.borrow().clone().unwrap();
        assert_eq!(req.method, "GET");
        assert!(req.url.contains(&format!("/ipfs/{cid}")), "{}", req.url);
        assert!(req.url.contains("format=raw"));
        // The trustless-gateway Accept + the bearer token are on the request.
        assert!(
            req.headers
                .iter()
                .any(|(k, v)| k == "Accept" && v == "application/vnd.ipld.raw")
        );
        assert!(
            req.headers
                .iter()
                .any(|(k, v)| k == "Authorization" && v == "Bearer secret")
        );
        // The block-level content-address check then re-witnesses it (bridge layer).
        assert_eq!(
            crate::bridge::fetch_verified(&gw, &cid).unwrap(),
            b"served by the gateway"
        );
    }

    #[test]
    fn gateway_client_maps_404_to_not_found_and_refuses_writes() {
        let cid = Cid::raw_blake3(b"absent at the gateway");
        let rec = ReqRecorder {
            status: 404,
            body: b"not found".to_vec(),
            ..Default::default()
        };
        let gw = GatewayClient::new("https://ipfs.example", rec);
        assert!(matches!(gw.get(&cid), Err(IpfsError::NotFound(_))));
        assert!(matches!(gw.put_raw(b"x"), Err(IpfsError::Unsupported(_))));
        assert!(matches!(gw.pin(&cid), Err(IpfsError::Unsupported(_))));
    }

    #[test]
    fn pinning_service_add_is_bearer_authed_json() {
        let cid = Cid::raw_blake3(b"durable content");
        let rec = ReqRecorder {
            status: 202,
            body: format!(r#"{{"requestid":"req-1","status":"queued","pin":{{"cid":"{cid}"}}}}"#)
                .into_bytes(),
            ..Default::default()
        };
        let svc = PinningServiceClient::new("https://api.pinning.example/psa", "TOKEN", rec);
        let status = svc.add(&cid, Some("my-site")).unwrap();
        assert_eq!(status.request_id, "req-1");
        assert_eq!(status.status, "queued");
        assert_eq!(status.cid, cid.to_string_cid());
        let req = svc.http.last.borrow().clone().unwrap();
        assert_eq!(req.method, "POST");
        assert!(req.url.ends_with("/pins"));
        assert!(
            req.headers
                .iter()
                .any(|(k, v)| k == "Authorization" && v == "Bearer TOKEN")
        );
        // The body carries the CID.
        let body: serde_json::Value = serde_json::from_slice(&req.body).unwrap();
        assert_eq!(body["cid"], cid.to_string_cid());
    }
}
