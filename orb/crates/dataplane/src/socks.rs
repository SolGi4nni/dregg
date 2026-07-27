//! SOCKS5 CONNECT egress handshake — driven by the proven decision.
//!
//! This module does NOT re-implement the handshake state machine. It owns only
//! socket I/O and the outbound client messages (greeting, optional auth, the
//! CONNECT request); every *decision* — advance, open the tunnel, or tear the
//! connection down on a malformed reply — is the proven `Socks.hstep`, crossed
//! through the `@[export drorb_socks_step]` byte seam (module `Reactor.Socks`).
//! The seam's no-early-egress gate (`hstep_no_early_egress`) is proven, so this
//! driver relays no application byte before the decision reaches `established`.
//!
//! The driver is bounded and crash-safe: a fixed handshake-byte cap and a fixed
//! step cap, no recursion, one fixed-size verdict allocation per step. An
//! adversarial or malformed peer is rejected in bounded work, never hangs or
//! grows unboundedly.

use std::io::{Read, Write};
use std::net::TcpStream;
use std::time::Duration;

// ---- The proven seam (Lean `@[export]`) + the ByteArray marshalling shim. ----

#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    // `Reactor.Socks.socksStep` — the deployed SOCKS5 handshake decision.
    // Input:  phaseByte :: authByte :: serverBuf
    // Output: nextPhase :: action :: consumedHi :: consumedLo   (always 4 bytes)
    fn drorb_socks_step(input: *mut LeanObject) -> *mut LeanObject;

    fn lean_initialize_runtime_module();
    fn lean_io_mark_end_initialization();
    #[link_name = "initialize_drorb_Reactor_Socks"]
    fn initialize_Reactor_Socks(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;

    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_world() -> *mut LeanObject;
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

/// Boot the Lean runtime and the `Reactor.Socks` module once. In the full
/// dataplane the runtime is already booted by the serve path; there this call
/// must be folded into that single global boot (add `initialize_Reactor_Socks`
/// beside `initialize_Dataplane`). Standalone, this is the whole boot sequence.
fn boot() {
    use std::sync::Once;
    static BOOT: Once = Once::new();
    BOOT.call_once(|| unsafe {
        lean_initialize_runtime_module();
        let res = initialize_Reactor_Socks(1, drorb_io_world());
        if drorb_io_ok(res) == 0 {
            panic!("initialize_Reactor_Socks returned an IO error");
        }
        drorb_obj_dec(res);
        lean_io_mark_end_initialization();
    });
}

// ---- Phase / action wire codes (must match `Reactor.Socks`). ----

pub const PHASE_AWAIT_GREETING: u8 = 0;
#[allow(dead_code)]
pub const PHASE_AWAIT_AUTH: u8 = 1;
#[allow(dead_code)]
pub const PHASE_AWAIT_REPLY: u8 = 2;
#[allow(dead_code)]
pub const PHASE_ESTABLISHED: u8 = 3;
#[allow(dead_code)]
pub const PHASE_FAILED: u8 = 4;

const ACT_WAIT: u8 = 0;
const ACT_SEND_AUTH: u8 = 1;
const ACT_SEND_CONNECT: u8 = 2;
const ACT_TUNNEL_UP: u8 = 3;
const ACT_CLOSE_ERR: u8 = 4;

/// The proven decision for one handshake step: the next phase, the egress
/// action, and how many leading server bytes the phase's parser drained.
#[derive(Clone, Copy, Debug)]
pub struct Verdict {
    pub next_phase: u8,
    pub action: u8,
    pub consumed: usize,
}

/// Cross the proven seam: run `Socks.hstep` on `(phase, has_auth, server_buf)`.
/// Total — every input yields a defined 4-byte verdict.
pub fn socks_step(phase: u8, has_auth: bool, server_buf: &[u8]) -> Verdict {
    boot();
    let mut input = Vec::with_capacity(2 + server_buf.len());
    input.push(phase);
    input.push(if has_auth { 1 } else { 0 });
    input.extend_from_slice(server_buf);
    // SAFETY: `drorb_sarray_of_bytes` copies `input` into a fresh owned Lean
    // ByteArray; the seam consumes it and returns an owned 4-byte ByteArray whose
    // bytes we read before dropping our reference. Pointers are valid until dec.
    unsafe {
        let inp = drorb_sarray_of_bytes(input.as_ptr(), input.len());
        let out = drorb_socks_step(inp);
        let n = drorb_sarray_len(out);
        let ptr = drorb_sarray_ptr(out);
        let slice = std::slice::from_raw_parts(ptr, n);
        let v = if n >= 4 {
            Verdict {
                next_phase: slice[0],
                action: slice[1],
                consumed: (slice[2] as usize) * 256 + slice[3] as usize,
            }
        } else {
            // The seam is total and always returns 4 bytes; treat any short
            // output as a fail-closed reject rather than trusting garbage.
            Verdict {
                next_phase: PHASE_FAILED,
                action: ACT_CLOSE_ERR,
                consumed: 0,
            }
        };
        drorb_obj_dec(out);
        v
    }
}

// ---- The CONNECT target + client message construction. ----

/// The final target the upstream SOCKS5 proxy should reach.
#[derive(Clone, Debug)]
pub enum Target {
    V4([u8; 4], u16),
    Domain(String, u16),
}

impl Target {
    /// The SOCKS5 CONNECT request (RFC 1928 §4):
    /// `VER(05) CMD(01) RSV(00) ATYP ADDR PORT`.
    fn connect_request(&self) -> Vec<u8> {
        let mut r = vec![0x05, 0x01, 0x00];
        match self {
            Target::V4(a, port) => {
                r.push(0x01);
                r.extend_from_slice(a);
                r.extend_from_slice(&port.to_be_bytes());
            }
            Target::Domain(host, port) => {
                let bytes = host.as_bytes();
                let len = bytes.len().min(255) as u8;
                r.push(0x03);
                r.push(len);
                r.extend_from_slice(&bytes[..len as usize]);
                r.extend_from_slice(&port.to_be_bytes());
            }
        }
        r
    }
}

/// Optional username/password credentials (RFC 1929).
#[derive(Clone, Debug)]
pub struct Creds {
    pub user: String,
    pub pass: String,
}

impl Creds {
    /// `VER(01) ULEN USER PLEN PASS`.
    fn auth_message(&self) -> Vec<u8> {
        let u = self.user.as_bytes();
        let p = self.pass.as_bytes();
        let ul = u.len().min(255) as u8;
        let pl = p.len().min(255) as u8;
        let mut m = vec![0x01, ul];
        m.extend_from_slice(&u[..ul as usize]);
        m.push(pl);
        m.extend_from_slice(&p[..pl as usize]);
        m
    }
}

#[derive(Debug, PartialEq)]
pub enum SocksError {
    /// The proven decision tore the connection down (`closeErr`): a refused
    /// method, an auth failure, a failure reply code, or a malformed reply.
    Rejected,
    /// The handshake exceeded its byte or step budget — bounded shutdown.
    Budget,
    /// A socket read/write failed, or the peer closed mid-handshake.
    Io,
}

/// Handshake safety budgets. A SOCKS5 handshake is a handful of tiny messages;
/// anything past these caps is a misbehaving or malicious peer and is dropped.
const MAX_HANDSHAKE_BYTES: usize = 4096;
const MAX_STEPS: usize = 64;
const READ_CHUNK: usize = 512;

/// Drive the SOCKS5 CONNECT handshake to open an egress tunnel to `target`
/// through the already-connected upstream proxy `stream`, calling the proven
/// decision at every step. On `Ok(())` the tunnel is established and the caller
/// may begin relaying application bytes; on `Err` nothing was relayed.
///
/// Every branch here is a mechanical response to the proven verdict — the host
/// never decides the protocol, only performs the I/O the decision dictates.
pub fn connect(
    stream: &mut TcpStream,
    target: &Target,
    creds: Option<&Creds>,
) -> Result<(), SocksError> {
    let has_auth = creds.is_some();
    stream
        .set_read_timeout(Some(Duration::from_secs(5)))
        .map_err(|_| SocksError::Io)?;

    // Greeting (RFC 1928 §3): offer no-auth, plus user/pass when we have creds.
    let greeting: &[u8] = if has_auth {
        &[0x05, 0x02, 0x00, 0x02]
    } else {
        &[0x05, 0x01, 0x00]
    };
    stream.write_all(greeting).map_err(|_| SocksError::Io)?;

    let mut phase = PHASE_AWAIT_GREETING;
    let mut buf: Vec<u8> = Vec::with_capacity(READ_CHUNK);
    let mut chunk = [0u8; READ_CHUNK];

    for _ in 0..MAX_STEPS {
        let v = socks_step(phase, has_auth, &buf);
        match v.action {
            ACT_TUNNEL_UP => {
                // Tunnel open — the proven gate has reached `established`.
                return Ok(());
            }
            ACT_CLOSE_ERR => {
                return Err(SocksError::Rejected);
            }
            ACT_SEND_AUTH => {
                buf.drain(..v.consumed.min(buf.len()));
                phase = v.next_phase;
                let msg = creds.map(|c| c.auth_message()).unwrap_or_default();
                stream.write_all(&msg).map_err(|_| SocksError::Io)?;
            }
            ACT_SEND_CONNECT => {
                buf.drain(..v.consumed.min(buf.len()));
                phase = v.next_phase;
                stream
                    .write_all(&target.connect_request())
                    .map_err(|_| SocksError::Io)?;
            }
            ACT_WAIT | _ => {
                // Need more server bytes for this phase — read one bounded chunk.
                if buf.len() >= MAX_HANDSHAKE_BYTES {
                    return Err(SocksError::Budget);
                }
                let n = stream.read(&mut chunk).map_err(|_| SocksError::Io)?;
                if n == 0 {
                    // Peer closed mid-handshake before the decision resolved.
                    return Err(SocksError::Io);
                }
                buf.extend_from_slice(&chunk[..n]);
            }
        }
    }
    Err(SocksError::Budget)
}

// ---------------------------------------------------------------------------
// My-hand end-to-end self-test: drive the REAL proven decision over a real
// loopback socket pair against an in-process fake SOCKS5 responder.
// ---------------------------------------------------------------------------

/// Exercise `connect` — hence every `socks_step` crossing into the proven
/// `Socks.hstep` gate — over a genuine TCP loopback pair against a minimal
/// in-process SOCKS5 responder that performs the no-auth method-select and a
/// success CONNECT reply. Returns `true` iff the driver reached `tunnelUp`
/// exactly as the proven decision dictates AND the responder saw a well-formed
/// greeting + CONNECT request. This is the socket-level wiring of the proven
/// decision: the host performs only the I/O each verdict names, and opens the
/// relay only on the proven `established`/`tunnelUp` gate.
///
/// Gated behind `DRORB_SOCKS_SELFTEST`; the serve path never calls it.
pub fn selftest() -> bool {
    use std::net::TcpListener;

    let listener = match TcpListener::bind("127.0.0.1:0") {
        Ok(l) => l,
        Err(_) => return false,
    };
    let addr = match listener.local_addr() {
        Ok(a) => a,
        Err(_) => return false,
    };

    // The fake upstream SOCKS5 proxy: no-auth method-select, then a success
    // CONNECT reply pointing at 127.0.0.1:80. It also validates that the driver
    // sent a well-formed RFC 1928 greeting and CONNECT request.
    let server = std::thread::spawn(move || -> bool {
        let (mut s, _) = match listener.accept() {
            Ok(x) => x,
            Err(_) => return false,
        };
        // Greeting: VER NMETHODS METHODS..
        let mut hdr = [0u8; 2];
        if s.read_exact(&mut hdr).is_err() || hdr[0] != 0x05 {
            return false;
        }
        let nmethods = hdr[1] as usize;
        let mut methods = vec![0u8; nmethods];
        if s.read_exact(&mut methods).is_err() || !methods.contains(&0x00) {
            return false;
        }
        // Method select: version 5, no-auth (0x00).
        if s.write_all(&[0x05, 0x00]).is_err() {
            return false;
        }
        // CONNECT request: VER CMD RSV ATYP ADDR PORT.
        let mut req = [0u8; 4];
        if s.read_exact(&mut req).is_err() || req[0] != 0x05 || req[1] != 0x01 {
            return false;
        }
        let addr_len = match req[3] {
            0x01 => 4,
            0x04 => 16,
            0x03 => {
                let mut l = [0u8; 1];
                if s.read_exact(&mut l).is_err() {
                    return false;
                }
                l[0] as usize
            }
            _ => return false,
        };
        let mut rest = vec![0u8; addr_len + 2];
        if s.read_exact(&mut rest).is_err() {
            return false;
        }
        // Success reply: VER REP RSV ATYP=v4 127.0.0.1 :80.
        s.write_all(&[0x05, 0x00, 0x00, 0x01, 127, 0, 0, 1, 0, 80])
            .is_ok()
    });

    let mut client = match TcpStream::connect(addr) {
        Ok(c) => c,
        Err(_) => return false,
    };
    let driver_ok = connect(&mut client, &Target::V4([127, 0, 0, 1], 80), None).is_ok();
    let server_ok = server.join().unwrap_or(false);
    driver_ok && server_ok
}
