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
    /// The transport (HTTP / socket) failed.
    Transport(String),
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
            IpfsError::Transport(e) => write!(f, "ipfs transport error: {e}"),
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

/// The minimal HTTP surface [`KuboClient`] needs: a single POST returning the
/// response body. Injecting this keeps `dregg-ipfs` free of any HTTP/TLS crate — the
/// gateway supplies a reqwest-backed impl, a local tool the bundled [`StdHttpPost`].
pub trait HttpPost {
    /// POST `body` (with `content_type`) to `url`; return the response body bytes.
    fn post(&self, url: &str, content_type: &str, body: Vec<u8>) -> Result<Vec<u8>, IpfsError>;
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
        Cid::parse(&hash).map_err(|e| IpfsError::BadResponse(format!("bad CID `{hash}`: {e}")))
    }

    fn get(&self, cid: &Cid) -> Result<Vec<u8>, IpfsError> {
        // `block/get` returns exactly the raw block bytes for a whole-blob pin.
        let url = format!("{}/api/v0/block/get?arg={}", self.base, cid.to_string_cid());
        self.http.post(&url, "application/octet-stream", Vec::new())
    }

    fn pin(&self, cid: &Cid) -> Result<(), IpfsError> {
        let url = format!("{}/api/v0/pin/add?arg={}", self.base, cid.to_string_cid());
        self.http
            .post(&url, "application/octet-stream", Vec::new())?;
        Ok(())
    }
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
#[derive(Clone, Debug, Default)]
pub struct StdHttpPost;

impl StdHttpPost {
    /// A new std transport.
    pub fn new() -> StdHttpPost {
        StdHttpPost
    }
}

impl HttpPost for StdHttpPost {
    fn post(&self, url: &str, content_type: &str, body: Vec<u8>) -> Result<Vec<u8>, IpfsError> {
        use std::io::{Read, Write};
        use std::net::TcpStream;

        let (host_port, path) = split_url(url)?;
        let mut stream = TcpStream::connect(&host_port)
            .map_err(|e| IpfsError::Transport(format!("connect {host_port}: {e}")))?;
        let req = format!(
            "POST {path} HTTP/1.1\r\nHost: {host_port}\r\nContent-Type: {content_type}\r\n\
             Content-Length: {}\r\nConnection: close\r\n\r\n",
            body.len()
        );
        stream
            .write_all(req.as_bytes())
            .and_then(|_| stream.write_all(&body))
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

/// Split an HTTP response into (status, headers-as-lowercased-map-ish, body),
/// decoding `Content-Length` or `Transfer-Encoding: chunked`. Returns the body on a
/// 2xx, else a [`IpfsError::Transport`] with the status + body snippet.
fn decode_http_response(raw: &[u8]) -> Result<Vec<u8>, IpfsError> {
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

    if (200..300).contains(&status) {
        Ok(body)
    } else {
        let snippet = String::from_utf8_lossy(&body)
            .chars()
            .take(200)
            .collect::<String>();
        Err(IpfsError::Transport(format!("HTTP {status}: {snippet}")))
    }
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
        assert_eq!(decode_http_response(ok).unwrap(), br#"{"Hash":"b"}"#);
        let err = b"HTTP/1.1 500 Internal Server Error\r\n\r\nboom";
        assert!(matches!(
            decode_http_response(err),
            Err(IpfsError::Transport(_))
        ));
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

    /// The real Kubo client compiles + formats correctly over a recording transport
    /// (no live daemon). This is the "the real client compiles + is shaped right"
    /// proof; a live round-trip is reviewed-go.
    #[test]
    fn kubo_client_formats_rpc_calls() {
        use std::cell::RefCell;

        #[derive(Default)]
        struct Recorder {
            last_url: RefCell<String>,
            reply: Vec<u8>,
        }
        impl HttpPost for Recorder {
            fn post(&self, url: &str, _ct: &str, _body: Vec<u8>) -> Result<Vec<u8>, IpfsError> {
                *self.last_url.borrow_mut() = url.to_string();
                Ok(self.reply.clone())
            }
        }

        let cid = Cid::raw_blake3(b"payload");
        let rec = Recorder {
            reply: format!(r#"{{"Name":"blob","Hash":"{}","Size":"7"}}"#, cid).into_bytes(),
            ..Default::default()
        };
        let client = KuboClient::local(rec);
        let got = client.put_raw(b"payload").unwrap();
        assert_eq!(got, cid, "add parses the returned CID");
        assert!(client.http.last_url.borrow().contains("hash=blake3"));
        assert!(client.http.last_url.borrow().contains("cid-version=1"));
    }
}
