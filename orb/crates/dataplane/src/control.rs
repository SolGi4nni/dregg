//! The gated ts2021 control-plane HTTP front-door: the two negotiation
//! endpoints a mesh-VPN node hits before it speaks the encrypted control
//! channel, plus the Upgrade→controlbase hand-off to the verified Noise
//! responder.
//!
//! This module is thin host glue — it owns the HTTP/1.1 request line, the header
//! parse, and the `101 Switching Protocols` upgrade dance, and nothing else. The
//! cryptography (Noise_IK X25519 + ChaCha20-Poly1305 + BLAKE2s) and the
//! coordination (register→authorize→map-poll→netmap, the ACL→packetFilter
//! compiler, MagicDNS, netmap→WireGuard) stay the verified Lean of `Control` /
//! `Control.Channel` / `Control.Acl`, exercised end-to-end by the `control-live`
//! responder. After the upgrade, the raw stream is spliced verbatim to that
//! verified responder; the host reads no plaintext off it.
//!
//! ## Routes (all constants cross-verified against the PUBLIC tailscale source)
//!
//! * `GET /key?v=<capVer>` → `200` JSON `{"legacy":"mkey:…","publicKey":"mkey:…"}`
//!   — the server's Noise responder static public key, which the client pins as
//!   the IK responder static `rs`. Field names + the `mkey:`+hex encoding are
//!   `tailcfg.OverTLSPublicKeyResponse` / `key.MachinePublic.AppendText`
//!   (`tailcfg/tailcfg.go`, `types/key/machine.go`: `machinePublicHexPrefix =
//!   "mkey:"`).
//! * `POST /ts2021` with `Upgrade: tailscale-control-protocol` +
//!   `Connection: Upgrade` → `101 Switching Protocols` echoing those two headers;
//!   the raw stream is now the controlbase channel. The path `/ts2021`
//!   (`control/controlhttp`: `serverUpgradePath`) and the upgrade value
//!   (`control/controlhttp/controlhttpcommon`: `UpgradeHeaderValue =
//!   "tailscale-control-protocol"`).
//!
//! ## The controlbase record framing (host message-boundary metadata)
//!
//! After the handshake, each control message is a record with a fixed 3-byte
//! header `[type:1][length:uint16 big-endian]` then the sealed payload
//! (`control/controlbase/messages.go`: `headerLen = 3`, `msgTypeRecord = 4`,
//! `maxMessageSize = 4096`). This is message-boundary framing — the same class
//! of metadata the HTTP/1.1 host framer already reads — and is implemented
//! host-side here; the sealed payload itself is opaque (produced/consumed only by
//! the verified AEAD in Lean). The `record_frame`/`record_deframe` helpers and the
//! `DRORB_CONTROL_SELFTEST` roundtrip demonstrate the layer.
//!
//! ## Hand-off and the long-poll
//!
//! On a successful upgrade the stream is spliced to the verified responder at
//! `DRORB_CONTROL_RESPONDER` (`host:port`, a running `control-live coord`). No
//! read timeout is set on that connection, so a `MapRequest{Stream:true}`
//! long-poll — the responder holding the connection open and streaming
//! `MapResponse` records with keep-alives as the netmap changes — is never
//! severed by the host. When no responder is configured, the upgraded stream is
//! served by the record-echo pump so the datapath is still exercisable my-hand.
//!
//! Gated on `DRORB_CONTROL_LISTEN`; the serve path and every other listener are
//! untouched when it is unset. Additive by construction.

use std::io::{Read, Write};
use std::net::{Shutdown, TcpListener, TcpStream, ToSocketAddrs};
use std::os::fd::{FromRawFd, IntoRawFd, RawFd};
use std::time::Duration;

// ---------------------------------------------------------------------------
// Wire constants — each cross-verified against the public tailscale source and
// cited at its definition site. NEVER fabricated from memory.
// ---------------------------------------------------------------------------

/// `control/controlhttp/controlhttpcommon`: `UpgradeHeaderValue`. The exact
/// `Upgrade:` value a stock client sends and the server must echo on the 101.
const UPGRADE_VALUE: &str = "tailscale-control-protocol";

/// `control/controlhttp/controlhttpcommon`: `HandshakeHeaderName`. The stock
/// controlhttp client carries the base64 Noise_IK **initiation** in THIS request
/// header on `POST /ts2021` (verified against tailscale v1.98.8: a real client's
/// header decodes to the byte-exact 101-byte `[ver:u16BE][type=1][len:u16BE][96]`
/// initiation frame the verified responder's `recvHandshakeFrame` consumes). The
/// server's Noise **response** is written on the raw connection after the 101
/// (controlhttpserver hijacks + writes to the socket), which is exactly the
/// responder's emitted response frame spliced back. Header lookup is
/// case-insensitive (`Head::header` lowercases), so the exact casing here is
/// documentation only.
const HANDSHAKE_HEADER: &str = "X-Tailscale-Handshake";

/// `control/controlbase/messages.go`: `msgTypeRecord = 4` (note: `msgTypeError`
/// is 3 — the post-handshake transport writes 4 in every record header, see
/// `control/controlbase/conn.go` `encryptLocked`). The other tags:
/// `msgTypeInitiation = 1`, `msgTypeResponse = 2`.
const MSG_TYPE_RECORD: u8 = 4;

/// `control/controlbase/messages.go`: `headerLen = 3` — `[type:1][len:u16 BE]`.
const RECORD_HEADER_LEN: usize = 3;

/// `control/controlbase/conn.go`: `maxMessageSize = 4096` (frame incl. header).
const MAX_MESSAGE_SIZE: usize = 4096;

/// The drorb-native test responder's static public key (x25519 base of the
/// `control-live` coord static). Serves `GET /key` when `DRORB_CONTROL_NOISE_PUB`
/// is unset. Override in production with the real responder static via that env.
const DEFAULT_NOISE_PUB_HEX: &str =
    "fa26f3e8a48dc027ef0df9fa80eb505244aaac90a6edb2dde0d5eaae533a9417";

// ---------------------------------------------------------------------------
// GET /key — the server Noise static pubkey (tailcfg.OverTLSPublicKeyResponse).
// ---------------------------------------------------------------------------

/// The configured server Noise responder static public key, hex (64 chars / 32
/// bytes). `DRORB_CONTROL_NOISE_PUB` overrides the drorb-native test default.
fn server_noise_pub_hex() -> String {
    std::env::var("DRORB_CONTROL_NOISE_PUB")
        .ok()
        .map(|s| s.trim().to_ascii_lowercase())
        .filter(|s| s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit()))
        .unwrap_or_else(|| DEFAULT_NOISE_PUB_HEX.to_string())
}

/// The `GET /key` JSON body. `key.MachinePublic` marshals as `mkey:` + 64 hex
/// (`types/key/machine.go`). `legacy` (the pre-Noise machine key) is the zero
/// key — modern clients read only `publicKey`
/// (`tailcfg.OverTLSPublicKeyResponse{ LegacyPublicKey json:"legacy",
/// PublicKey json:"publicKey" }`).
fn key_json() -> String {
    let pub_hex = server_noise_pub_hex();
    let zero = "0".repeat(64);
    format!("{{\"legacy\":\"mkey:{zero}\",\"publicKey\":\"mkey:{pub_hex}\"}}")
}

// ---------------------------------------------------------------------------
// Base64 decode for the X-Tailscale-Handshake header (transport metadata).
// ---------------------------------------------------------------------------

/// RFC 4648 standard-alphabet base64 decode (`+`/`/`, `=` padding). Total and
/// bounded: any invalid character, bad length, or misplaced padding is a clean
/// `None`, never a panic. This decodes host-side TRANSPORT metadata (the
/// `X-Tailscale-Handshake` request header value) — the same class as the HTTP
/// head parse above; it is NOT cryptography. The decoded bytes are the opaque
/// Noise initiation frame, handed verbatim to the verified responder.
fn b64_decode(s: &str) -> Option<Vec<u8>> {
    fn val(b: u8) -> Option<u8> {
        match b {
            b'A'..=b'Z' => Some(b - b'A'),
            b'a'..=b'z' => Some(b - b'a' + 26),
            b'0'..=b'9' => Some(b - b'0' + 52),
            b'+' => Some(62),
            b'/' => Some(63),
            _ => None,
        }
    }
    let s = s.trim().as_bytes();
    if s.is_empty() || s.len() % 4 != 0 {
        return None;
    }
    let nchunks = s.len() / 4;
    let mut out = Vec::with_capacity(nchunks * 3);
    for (ci, chunk) in s.chunks(4).enumerate() {
        let is_last = ci + 1 == nchunks;
        let mut acc = 0u32;
        let mut pad = 0usize;
        for (i, &b) in chunk.iter().enumerate() {
            if b == b'=' {
                // Padding is only valid in the final chunk, in the last one or
                // two positions, and must be contiguous at the end.
                if !is_last || i < 2 || pad >= 2 {
                    return None;
                }
                pad += 1;
                acc <<= 6;
            } else {
                if pad != 0 {
                    return None; // a non-'=' after a '=' — malformed
                }
                acc = (acc << 6) | val(b)? as u32;
            }
        }
        out.push((acc >> 16) as u8);
        if pad < 2 {
            out.push((acc >> 8) as u8);
        }
        if pad < 1 {
            out.push(acc as u8);
        }
    }
    Some(out)
}

// ---------------------------------------------------------------------------
// The controlbase record framing (host-side message-boundary metadata).
// ---------------------------------------------------------------------------

/// Frame one already-sealed record payload as `[type=4][len:u16 BE][payload]`.
/// `None` if the payload does not fit a record (header+payload > maxMessageSize),
/// matching the wire's length bound.
pub fn record_frame(sealed: &[u8]) -> Option<Vec<u8>> {
    if sealed.len() + RECORD_HEADER_LEN > MAX_MESSAGE_SIZE || sealed.len() > u16::MAX as usize {
        return None;
    }
    let n = sealed.len() as u16;
    let mut out = Vec::with_capacity(RECORD_HEADER_LEN + sealed.len());
    out.push(MSG_TYPE_RECORD);
    out.extend_from_slice(&n.to_be_bytes());
    out.extend_from_slice(sealed);
    Some(out)
}

/// Deframe the leading record off a wire prefix: returns the sealed payload and
/// the octet count consumed, or `None` if the prefix is not (yet) one complete,
/// well-typed record. Total and bounded — a malformed or short prefix is a clean
/// `None`, never a panic.
pub fn record_deframe(prefix: &[u8]) -> Option<(Vec<u8>, usize)> {
    if prefix.len() < RECORD_HEADER_LEN || prefix[0] != MSG_TYPE_RECORD {
        return None;
    }
    let len = u16::from_be_bytes([prefix[1], prefix[2]]) as usize;
    let end = RECORD_HEADER_LEN + len;
    if len + RECORD_HEADER_LEN > MAX_MESSAGE_SIZE || prefix.len() < end {
        return None;
    }
    Some((prefix[RECORD_HEADER_LEN..end].to_vec(), end))
}

// ---------------------------------------------------------------------------
// The HTTP request head parse (thin — request line + a lowercase header map).
// ---------------------------------------------------------------------------

struct Head {
    method: Vec<u8>,
    /// Path without the query string.
    path: Vec<u8>,
    /// `(lowercased-name, raw-value-trimmed)` pairs.
    headers: Vec<(String, String)>,
}

impl Head {
    fn header(&self, name: &str) -> Option<&str> {
        let n = name.to_ascii_lowercase();
        self.headers
            .iter()
            .find(|(k, _)| *k == n)
            .map(|(_, v)| v.as_str())
    }

    /// A header whose comma-separated token set contains `token`
    /// (case-insensitive) — `Connection: keep-alive, Upgrade`.
    fn header_has_token(&self, name: &str, token: &str) -> bool {
        self.header(name)
            .map(|v| v.split(',').any(|t| t.trim().eq_ignore_ascii_case(token)))
            .unwrap_or(false)
    }
}

/// Parse the request head (already read up to and including the blank line).
fn parse_head(buf: &[u8]) -> Option<Head> {
    let head_end = buf
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 4)
        .unwrap_or(buf.len());
    let head = &buf[..head_end];
    let mut lines = head.split(|&b| b == b'\n');

    let request_line = lines.next()?;
    let request_line = request_line.strip_suffix(b"\r").unwrap_or(request_line);
    let mut parts = request_line.split(|&b| b == b' ');
    let method = parts.next()?.to_vec();
    let raw_path = parts.next()?;
    let path = raw_path
        .split(|&b| b == b'?')
        .next()
        .unwrap_or(raw_path)
        .to_vec();

    let mut headers = Vec::new();
    for line in lines {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if line.is_empty() {
            continue;
        }
        if let Some(colon) = line.iter().position(|&b| b == b':') {
            let name = String::from_utf8_lossy(&line[..colon])
                .trim()
                .to_ascii_lowercase();
            let value = String::from_utf8_lossy(&line[colon + 1..])
                .trim()
                .to_string();
            if !name.is_empty() {
                headers.push((name, value));
            }
        }
    }
    Some(Head {
        method,
        path,
        headers,
    })
}

/// Read the request head (until the blank line, capped). Returns the bytes read
/// including any surplus already on the wire after the head (unused here — the
/// upgrade replies before the client sends body bytes).
fn read_head(stream: &mut TcpStream) -> std::io::Result<Vec<u8>> {
    let mut buf = Vec::with_capacity(1024);
    let mut chunk = [0u8; 1024];
    loop {
        let n = stream.read(&mut chunk)?;
        if n == 0 {
            break;
        }
        buf.extend_from_slice(&chunk[..n]);
        if buf.windows(4).any(|w| w == b"\r\n\r\n") || buf.len() > 16 << 10 {
            break;
        }
    }
    Ok(buf)
}

// ---------------------------------------------------------------------------
// Response builders.
// ---------------------------------------------------------------------------

fn simple_response(status: u16, reason: &str, content_type: &str, body: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(body.len() + 160);
    out.extend_from_slice(
        format!(
            "HTTP/1.1 {status} {reason}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
            body.len()
        )
        .as_bytes(),
    );
    out.extend_from_slice(body);
    out
}

/// The `101 Switching Protocols` head that turns the connection into the raw
/// controlbase stream. Echoes the exact `Upgrade`/`Connection` values a stock
/// client's http.Transport requires to complete the switch. No body follows.
fn switching_protocols() -> Vec<u8> {
    format!(
        "HTTP/1.1 101 Switching Protocols\r\nUpgrade: {UPGRADE_VALUE}\r\nConnection: Upgrade\r\n\r\n"
    )
    .into_bytes()
}

// ---------------------------------------------------------------------------
// The verified-TLS terminator seam (DRORB_CONTROL_TLS).
//
// When `DRORB_CONTROL_TLS=1`, each accepted connection is a TLS 1.3 stream. Its
// raw fd is handed to the Lean `drorb_tls_terminate` export — the SAME verified
// handshake + record layer as `drorb_tls_serve` (every `serverStep`/`chooseCert`/
// `kexStep` theorem, the PQ-hybrid pin), but with the decrypted byte stream
// PUMPED to one end of a loopback duplex pair instead of `drorbServe`. The
// UNMODIFIED [`handle`] runs over the OTHER end, so `GET /key`, `POST /ts2021`
// (Upgrade -> 101) and the controlbase splice all run over the decrypted stream
// with NO logic change here. No new TLS stack crosses this seam: the crypto is
// the proven `appStep`/`sealAppData` record layer, and the binary stays ldd-clean
// of libssl.
// ---------------------------------------------------------------------------

/// Opaque Lean heap object; only ever held and passed as `*mut`.
type LeanObj = core::ffi::c_void;

// The marshalling shims (`drorb_sarray_of_bytes` / `_obj_dec` / `_io_world`) are
// the SAME C symbols `serve.rs` / `captp.rs` declare against their own private
// opaque `LeanObject`; we name the object `c_void` here. All are thin pointers,
// so the ABI is identical — the nominal-type mismatch across modules is
// intentional and safe.
#[allow(clashing_extern_declarations)]
unsafe extern "C" {
    /// `@[export drorb_tls_terminate] Dataplane.Tls.drorbTlsTerminate : UInt32 ->
    /// ByteArray^8 -> UInt32 -> IO Unit`. Runs the verified TLS server on `tls_fd`
    /// and pumps the decrypted duplex stream to/from `plain_fd` (one end of a
    /// loopback pair). The eight certificate ByteArrays are the SAME pool material
    /// `drorb_tls_serve` takes (Ed25519 default cert/seed, then the optional
    /// ECDSA-P256 and RSA-PSS-2048 leaves; an EMPTY ByteArray means "absent").
    /// Both fds are consumed and closed by the Lean side.
    fn drorb_tls_terminate(
        tls_fd: u32,
        cert: *mut LeanObj,
        seed: *mut LeanObj,
        ecdsa_cert: *mut LeanObj,
        ecdsa_priv: *mut LeanObj,
        rsa_cert: *mut LeanObj,
        rsa_n: *mut LeanObj,
        rsa_e: *mut LeanObj,
        rsa_d: *mut LeanObj,
        plain_fd: u32,
        world: *mut LeanObj,
    ) -> *mut LeanObj;

    // Byte-marshalling adapter (ffi/drorb_ffi.c) — the SAME shim serve.rs uses.
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObj;
    fn drorb_obj_dec(o: *mut LeanObj);
    fn drorb_io_world() -> *mut LeanObj;

    // Register a thread the Lean runtime did not create, before its first
    // crossing. The process-global runtime is already booted by the serve
    // gateway (`serve::spawn_serve_thread` in `main`, before this listener runs).
    fn lean_initialize_thread();

    // Create the process-global Lean TASK MANAGER. Without it `lean_task_spawn`
    // has no scheduler to enqueue onto and runs the spawned closure INLINE on the
    // calling thread — `IO.asTask` silently degrades to a synchronous call. The
    // terminator's `enterPump` spawns its inbound pump exactly that way, so with
    // no manager the two pumps SERIALIZE: the inbound pump owns the thread
    // blocking on the TLS fd until the client closes, and the host's response
    // sits unread in the loopback buffer the whole time. See `ensure_task_manager`.
    fn lean_init_task_manager();
}

/// Ensure the Lean task manager exists before the first `IO.asTask` in this
/// process. `lean_initialize_runtime_module` (what the serve gateway calls at
/// boot) does NOT create it, and a null manager makes `lean_task_spawn` run the
/// closure inline instead of concurrently — which deadlocks any Lean code whose
/// correctness depends on two tasks making progress together, as the TLS
/// terminator's duplex pump pair does.
///
/// Called once, from `run_control` BEFORE the listener accepts anything, so the
/// global is published while no other thread can be inside `lean_task_spawn`.
pub(crate) fn ensure_task_manager() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    // SAFETY: the process-global Lean runtime is booted by the serve gateway in
    // `main` before `run_control` runs, and `Once` publishes the manager pointer
    // before any connection thread can reach a Lean task spawn.
    ONCE.call_once(|| unsafe { lean_init_task_manager() });
}

/// Cross the `drorb_tls_terminate` seam on the CURRENT (already runtime-attached)
/// thread and block for the connection's lifetime. Each pool member is copied
/// into a fresh owned Lean ByteArray the export consumes; `tls_fd` and `plain_fd`
/// are consumed and closed by the Lean side.
fn run_tls_terminate(tls_fd: RawFd, cert: &crate::tls::TlsCert, plain_fd: RawFd) {
    // SAFETY: the byte pointers live for the duration of each `drorb_sarray_of_bytes`
    // copy; the returned IO-result object is released with `drorb_obj_dec`. The
    // calling thread was registered with `lean_initialize_thread` before this call.
    unsafe {
        let ba = |v: &[u8]| drorb_sarray_of_bytes(v.as_ptr(), v.len());
        let c = ba(&cert.cert_der);
        let s = ba(&cert.seed);
        let ec = ba(&cert.ecdsa_cert);
        let ep = ba(&cert.ecdsa_priv);
        let rc = ba(&cert.rsa_cert);
        let rn = ba(&cert.rsa_n);
        let re = ba(&cert.rsa_e);
        let rd = ba(&cert.rsa_d);
        let world = drorb_io_world();
        let res = drorb_tls_terminate(
            tls_fd as u32,
            c,
            s,
            ec,
            ep,
            rc,
            rn,
            re,
            rd,
            plain_fd as u32,
            world,
        );
        drorb_obj_dec(res);
    }
}

/// Build a loopback TCP duplex pair `(plain_a, plain_b_fd)`. `plain_a` is a real
/// `TcpStream` the UNMODIFIED [`handle`] runs over; `plain_b_fd` is the raw fd the
/// Lean terminator pumps decrypted bytes through. A genuine loopback `TcpStream`
/// (not a Unix socket) keeps `handle`'s `TcpStream` signature untouched.
fn loopback_pair() -> std::io::Result<(TcpStream, RawFd)> {
    let lst = TcpListener::bind("127.0.0.1:0")?;
    let addr = lst.local_addr()?;
    let plain_b = TcpStream::connect(addr)?;
    let (plain_a, _) = lst.accept()?;
    plain_a.set_nodelay(true).ok();
    plain_b.set_nodelay(true).ok();
    Ok((plain_a, plain_b.into_raw_fd()))
}

/// Terminate one accepted TLS connection over the verified server, then run the
/// UNMODIFIED control [`handle`] over the decrypted stream. The terminator owns a
/// dedicated runtime-attached thread (it blocks for the connection's lifetime);
/// `handle` runs on the current thread. When `handle` returns it drops its end of
/// the pair, the Lean outbound pump sees EOF, sends `close_notify`, and closes.
/// **The verified-TLS crossing, factored.** Take an accepted TLS connection, hand
/// its fd to the Lean `drorb_tls_terminate` export on a dedicated runtime-attached
/// thread together with one end of a loopback duplex pair, and return the OTHER end —
/// a plain `TcpStream` carrying the decrypted bidirectional byte stream — plus the
/// terminator's join handle.
///
/// This is the ONLY place the crossing is made. The ts2021 control front runs its
/// unmodified `handle` over the returned stream; the DERP front
/// (`crate::derp_front`) splices the returned stream to the verified Lean relay.
/// Neither grows a TLS path of its own: the handshake, record layer, cert selection
/// and ALPN pin are all the proven Lean.
pub(crate) fn terminate_tls(
    tls_stream: TcpStream,
    cert: std::sync::Arc<crate::tls::TlsCert>,
    thread_name: &str,
) -> std::io::Result<(TcpStream, std::thread::JoinHandle<()>)> {
    let (plain_a, plain_b_fd) = loopback_pair()?;
    let tls_fd = tls_stream.into_raw_fd();
    let term = std::thread::Builder::new()
        .name(thread_name.to_string())
        .spawn(move || {
            // SAFETY: the serve gateway booted the process-global Lean runtime in
            // `main` before this listener accepted, so registering this thread
            // once before its first crossing is exactly the attached-owner
            // contract (`serve::spawn_attached_owner`).
            unsafe { lean_initialize_thread() };
            run_tls_terminate(tls_fd, &cert, plain_b_fd);
        });
    match term {
        Ok(t) => Ok((plain_a, t)),
        Err(e) => {
            // SAFETY: reclaim ownership of the fds we handed out so they close.
            unsafe {
                let _ = TcpStream::from_raw_fd(tls_fd);
                let _ = TcpStream::from_raw_fd(plain_b_fd);
            }
            drop(plain_a);
            Err(e)
        }
    }
}

fn handle_tls(tls_stream: TcpStream, cert: std::sync::Arc<crate::tls::TlsCert>) {
    match terminate_tls(tls_stream, cert, "drorb-control-tls") {
        Ok((plain_a, t)) => {
            handle(plain_a);
            let _ = t.join();
        }
        Err(e) => eprintln!("dataplane: control TLS — terminator crossing failed: {e}"),
    }
}

// ---------------------------------------------------------------------------
// The connection handler.
// ---------------------------------------------------------------------------

fn handle(mut stream: TcpStream) {
    // A short read timeout for the HTTP head only. It is CLEARED before any
    // upgrade splice so a streaming long-poll is never severed.
    stream.set_read_timeout(Some(Duration::from_secs(10))).ok();
    stream.set_nodelay(true).ok();

    let buf = match read_head(&mut stream) {
        Ok(b) if !b.is_empty() => b,
        _ => return,
    };
    let head = match parse_head(&buf) {
        Some(h) => h,
        None => {
            let _ = stream.write_all(&simple_response(
                400,
                "Bad Request",
                "text/plain; charset=utf-8",
                b"bad request\n",
            ));
            return;
        }
    };

    match (head.method.as_slice(), head.path.as_slice()) {
        (b"GET", b"/key") => {
            let _ = stream.write_all(&simple_response(
                200,
                "OK",
                "application/json",
                key_json().as_bytes(),
            ));
        }
        (b"POST", b"/ts2021") => {
            let upgrade_ok = head
                .header("upgrade")
                .map(|v| v.eq_ignore_ascii_case(UPGRADE_VALUE))
                .unwrap_or(false);
            let connection_ok = head.header_has_token("connection", "upgrade");
            if upgrade_ok && connection_ok {
                // The stock controlhttp client carries the Noise_IK initiation in
                // the X-Tailscale-Handshake request header (base64), NOT on the
                // post-101 wire. Decode it here so it can be handed to the
                // verified responder as its first wire bytes; the responder reads
                // it via recvHandshakeFrame exactly as if it had arrived inline.
                // An absent/malformed header yields an empty initiation (nothing
                // injected) — the connection then behaves as the pre-header wire
                // protocol (the drorb-native coord/node path).
                let init = head
                    .header(HANDSHAKE_HEADER)
                    .and_then(b64_decode)
                    .unwrap_or_default();
                if stream.write_all(&switching_protocols()).is_ok() {
                    let _ = stream.flush();
                    // The stream is now the raw controlbase channel. Clear the
                    // head-read timeout so the long-poll can stay open.
                    stream.set_read_timeout(None).ok();
                    drive_controlbase(stream, init);
                }
            } else {
                // Correct method, but the client did not ask to upgrade.
                let body = b"ts2021 requires Upgrade: tailscale-control-protocol\n";
                let mut out = Vec::new();
                out.extend_from_slice(
                    format!(
                        "HTTP/1.1 426 Upgrade Required\r\nUpgrade: {UPGRADE_VALUE}\r\nConnection: close\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: {}\r\n\r\n",
                        body.len()
                    )
                    .as_bytes(),
                );
                out.extend_from_slice(body);
                let _ = stream.write_all(&out);
            }
        }
        // Known paths, wrong method → 405.
        (_, b"/key") | (_, b"/ts2021") => {
            let _ = stream.write_all(&simple_response(
                405,
                "Method Not Allowed",
                "text/plain; charset=utf-8",
                b"method not allowed\n",
            ));
        }
        _ => {
            let _ = stream.write_all(&simple_response(
                404,
                "Not Found",
                "text/plain; charset=utf-8",
                b"not found\n",
            ));
        }
    }
}

/// After the 101, own the raw controlbase stream. If a verified responder is
/// configured (`DRORB_CONTROL_RESPONDER=host:port`, a running `control-live
/// coord`), splice the stream to it verbatim — every handshake message and every
/// sealed record moves byte-for-byte between the client and the verified Noise
/// responder, which drives the proven register→authorize→map-poll pipeline and
/// holds the connection open for the `MapRequest{Stream:true}` long-poll. With no
/// responder configured, run the bounded record-echo pump so the upgraded
/// datapath is still exercisable.
fn drive_controlbase(stream: TcpStream, init: Vec<u8>) {
    match std::env::var("DRORB_CONTROL_RESPONDER") {
        Ok(addr) if !addr.trim().is_empty() => match TcpStream::connect(addr.trim()) {
            Ok(mut upstream) => {
                // Replay the header-carried Noise initiation to the responder as
                // the first bytes of the controlbase stream, then splice the rest
                // of the duplex verbatim. The responder's handshake response is
                // written back on the raw connection by the same splice — exactly
                // where the stock client reads it (controlhttpserver hijacks and
                // writes the response to the socket after the 101).
                if !init.is_empty() {
                    if upstream.write_all(&init).is_err() {
                        let _ = stream.shutdown(Shutdown::Both);
                        let _ = upstream.shutdown(Shutdown::Both);
                        return;
                    }
                }
                splice(stream, upstream)
            }
            Err(e) => {
                eprintln!("dataplane: control upgrade — responder {addr} unreachable: {e}");
                let _ = stream.shutdown(Shutdown::Both);
            }
        },
        _ => record_echo(stream),
    }
}

/// Bidirectional verbatim splice between the upgraded client stream and the
/// verified responder — the host moves bytes and holds no protocol state. No
/// read timeout on either side, so a long-poll stream is never severed by the
/// host.
fn splice(client: TcpStream, upstream: TcpStream) {
    let (mut c_read, mut c_write) = match (client.try_clone(), client) {
        (Ok(r), w) => (r, w),
        (Err(_), w) => {
            let _ = w.shutdown(Shutdown::Both);
            return;
        }
    };
    let (mut u_read, mut u_write) = match (upstream.try_clone(), upstream) {
        (Ok(r), w) => (r, w),
        (Err(_), w) => {
            let _ = w.shutdown(Shutdown::Both);
            let _ = c_write.shutdown(Shutdown::Both);
            return;
        }
    };
    let up = std::thread::spawn(move || {
        let _ = std::io::copy(&mut c_read, &mut u_write);
        let _ = u_write.shutdown(Shutdown::Write);
    });
    let _ = std::io::copy(&mut u_read, &mut c_write);
    let _ = c_write.shutdown(Shutdown::Write);
    let _ = up.join();
}

/// The no-responder fallback: accumulate the upgraded stream, and for each
/// complete controlbase record echo its canonical re-framing back. Governs the
/// bytes through the same `[type:4][len:u16 BE]` framer the real channel rides,
/// with no crypto (the payload is echoed opaque) — a my-hand exercise of the
/// upgraded record datapath. Bounded: a malformed/oversized prefix closes the
/// connection.
fn record_echo(mut stream: TcpStream) {
    let mut acc: Vec<u8> = Vec::with_capacity(MAX_MESSAGE_SIZE);
    let mut chunk = [0u8; MAX_MESSAGE_SIZE];
    loop {
        let n = match stream.read(&mut chunk) {
            Ok(0) => break,
            Ok(n) => n,
            Err(_) => break,
        };
        acc.extend_from_slice(&chunk[..n]);
        if acc.len() > MAX_MESSAGE_SIZE {
            // A record cannot exceed one max frame; refuse to buffer past it.
            break;
        }
        while let Some((payload, used)) = record_deframe(&acc) {
            match record_frame(&payload) {
                Some(reframed) => {
                    if stream.write_all(&reframed).is_err() {
                        return;
                    }
                }
                None => return,
            }
            acc.drain(..used);
        }
    }
    let _ = stream.shutdown(Shutdown::Both);
}

// ---------------------------------------------------------------------------
// The gated listener + a my-hand record-codec self-test.
// ---------------------------------------------------------------------------

/// Run the gated ts2021 control front-door: accept connections and answer
/// `GET /key` / `POST /ts2021` (Upgrade→controlbase), one thread per connection.
/// Never returns while the listener is live.
pub fn run_control(listener: TcpListener) {
    let local = listener
        .local_addr()
        .map(|a| a.to_string())
        .unwrap_or_else(|_| "?".to_string());
    let responder = std::env::var("DRORB_CONTROL_RESPONDER").unwrap_or_default();
    let sink = if responder.trim().is_empty() {
        "record-echo (no responder configured)".to_string()
    } else {
        format!("verified responder {}", responder.trim())
    };
    // Verified-TLS terminator (DRORB_CONTROL_TLS=1): each accepted connection is a
    // TLS 1.3 stream terminated over the proven server before `handle` runs. The
    // certificate pool loads once (the same `DRORB_TLS_*` material the HTTPS front
    // door uses). Unset / non-"1" leaves the front plaintext, byte-for-byte as
    // before.
    let tls_cert: Option<std::sync::Arc<crate::tls::TlsCert>> = if std::env::var(
        "DRORB_CONTROL_TLS",
    )
    .ok()
    .as_deref()
        == Some("1")
    {
        // The terminator's duplex pump pair needs REAL task concurrency.
        ensure_task_manager();
        match crate::tls::load_cert() {
            Some(c) => Some(std::sync::Arc::new(c)),
            None => {
                eprintln!(
                    "dataplane: DRORB_CONTROL_TLS=1 but no usable cert — serving PLAINTEXT control front"
                );
                None
            }
        }
    } else {
        None
    };
    eprintln!(
        "dataplane: ts2021 control front-door on {local} \
         (GET /key -> Noise pubkey; POST /ts2021 + Upgrade -> 101 -> {sink}){}",
        if tls_cert.is_some() {
            " over VERIFIED TLS 1.3 (drorb_tls_terminate)"
        } else {
            ""
        }
    );
    for conn in listener.incoming() {
        match conn {
            Ok(stream) => {
                let cert = tls_cert.clone();
                std::thread::Builder::new()
                    .name("drorb-control-conn".into())
                    .spawn(move || match cert {
                        Some(c) => handle_tls(stream, c),
                        None => handle(stream),
                    })
                    .ok();
            }
            Err(_) => continue,
        }
    }
}

/// `DRORB_CONTROL_SELFTEST`: a my-hand roundtrip of the controlbase record
/// framer over a set of boundary payload sizes, then exit. Off by default.
pub fn selftest() -> i32 {
    let cases: [usize; 6] = [0, 1, 3, 64, 4080, MAX_MESSAGE_SIZE - RECORD_HEADER_LEN];
    let mut ok = true;
    for &len in &cases {
        let payload: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
        match record_frame(&payload) {
            Some(framed) => {
                let header_ok = framed[0] == MSG_TYPE_RECORD
                    && u16::from_be_bytes([framed[1], framed[2]]) as usize == len;
                // Deframe the frame plus a trailing byte to prove the consumed
                // count is exact (does not over-read the tail).
                let mut with_tail = framed.clone();
                with_tail.push(0xAA);
                match record_deframe(&with_tail) {
                    Some((got, used)) => {
                        let roundtrip = got == payload && used == RECORD_HEADER_LEN + len;
                        println!(
                            "record[{len:>4}B] frame={}B header_ok={header_ok} roundtrip={roundtrip} consumed_exact={}",
                            framed.len(),
                            used == RECORD_HEADER_LEN + len
                        );
                        ok &= header_ok && roundtrip;
                    }
                    None => {
                        println!("record[{len:>4}B] deframe FAILED");
                        ok = false;
                    }
                }
            }
            None => {
                println!("record[{len:>4}B] frame FAILED");
                ok = false;
            }
        }
    }
    // A short prefix must be a clean None (not a panic, not a false frame).
    let partial = record_deframe(&[MSG_TYPE_RECORD, 0x00, 0x40, 0x01]);
    let partial_ok = partial.is_none();
    // A wrong type tag must be rejected.
    let wrong_type = record_deframe(&[0x03, 0x00, 0x00]);
    let wrong_type_ok = wrong_type.is_none();
    println!("short-prefix -> None: {partial_ok}   wrong-type(3) -> None: {wrong_type_ok}");
    ok &= partial_ok && wrong_type_ok;
    if ok {
        println!("CONTROL RECORD CODEC SELFTEST: PASS");
        0
    } else {
        eprintln!("CONTROL RECORD CODEC SELFTEST: FAIL");
        1
    }
}

/// Resolve a listen spec (a bare `PORT` binds loopback, like the sibling gated
/// listeners) to a bound `TcpListener`. Mirrors `main::bind_listener` semantics
/// but local so the module is self-contained for the self-test path.
pub fn bind(spec: &str) -> std::io::Result<TcpListener> {
    let addr = if spec.contains(':') {
        spec.to_string()
    } else {
        format!("127.0.0.1:{spec}")
    };
    let mut last_err = None;
    for sa in addr.to_socket_addrs()? {
        match TcpListener::bind(sa) {
            Ok(l) => return Ok(l),
            Err(e) => last_err = Some(e),
        }
    }
    Err(last_err
        .unwrap_or_else(|| std::io::Error::new(std::io::ErrorKind::Other, "no address resolved")))
}
