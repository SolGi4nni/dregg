//! The verified outbound (client) path: dial an upstream, put a request on the
//! wire, and parse the response **as a verified client**.
//!
//! The reverse proxy's existing forward (`proxy_dial`) moves upstream response
//! bytes to the client verbatim — it never parses them. This module is the step
//! beyond byte-forwarding: it crosses the proven response parser
//! (`Proto.ResponseParse.parse`, exported as `drorb_response_parse`) and the
//! proven request serializer (`Proto.RequestSerialize.serialize`, exported as
//! `drorb_request_serialize`), so the framing the host acts on (status code,
//! body length) is the one the *verified* parser resolved, not an ad-hoc scan.
//!
//! The client core is the symmetric dual of the server's `drorb_serve`: the
//! server parses inbound requests and serializes responses; this parses inbound
//! responses and serializes outbound requests. Both round-trips are proven
//! (`parse (serialize …) = …`), so a drorb client and a drorb server agree on
//! every byte in both directions.
//!
//! Like every Lean seam, the crossings run on the runtime-owner thread (the Lean
//! runtime is a process-global singleton); [`boot_client_runtime`] initializes
//! the client module's closure once. The existing streaming passthrough in
//! `proxy_dial` is untouched — this is an additive, opt-in verified path.

use std::io::{Read, Write};
use std::net::{SocketAddr, TcpStream};
use std::time::Duration;

#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    fn lean_initialize_runtime_module();
    fn lean_io_mark_end_initialization();
    /// `initialize_Client_H1` — brings up the verified client module and its
    /// whole import closure (request serializer, response parser, decimal inverse).
    #[link_name = "initialize_drorb_Client_H1"]
    fn initialize_Client_H1(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_response_parse]` — response bytes in; on success
    /// `1 :: <decimal status> :: 0 :: <body>`, on a parse failure the byte `0`.
    fn drorb_response_parse(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_request_serialize]` — `mLen::method::tLen::target::vLen::
    /// version` in, the serialized request line + blank line out.
    fn drorb_request_serialize(input: *mut LeanObject) -> *mut LeanObject;
    /// `initialize_Client_FetchExport` — brings up the verified H2 client seam
    /// (`Client.H2` submit + `Client.H2Receive` reassembly + the real Huffman decoder).
    #[link_name = "initialize_drorb_Client_FetchExport"]
    fn initialize_Client_FetchExport(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_h2_request]` — `aLen::authority::pLen::path` in; the proven
    /// `Client.H2.requestBytes` client submit octets out (preface + SETTINGS + HEADERS).
    fn drorb_h2_request(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_h2_response]` — the raw H2 response frame bytes in; on success
    /// `1 :: <ASCII status> :: 0 :: <body>`, on a receive failure the byte `0`.
    fn drorb_h2_response(input: *mut LeanObject) -> *mut LeanObject;

    // Byte-marshalling adapter (ffi/drorb_ffi.c).
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_world() -> *mut LeanObject;
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

/// Initialize the Lean runtime for the client seam. Call once, on the thread
/// that will own the runtime, before any crossing. Idempotent guards belong to
/// the caller (the process-global runtime must be booted exactly once).
pub fn boot_client_runtime() {
    // SAFETY: the standard leanc module-init sequence; run once on the owner thread.
    unsafe {
        lean_initialize_runtime_module();
        let res = initialize_Client_H1(1, drorb_io_world());
        if drorb_io_ok(res) == 0 {
            panic!("initialize_Client_H1 returned an IO error");
        }
        drorb_obj_dec(res);
        lean_io_mark_end_initialization();
    }
}

/// Initialize the verified H2 client seam (`Client.FetchExport`). Call once, on
/// the runtime-owner thread, after [`boot_client_runtime`]. Brings up the H2
/// submit + receive closure so `drorb_h2_request` / `drorb_h2_response` can cross.
pub fn boot_h2_client() {
    // SAFETY: the standard leanc module-init sequence for a second export module,
    // run once on the owner thread after the runtime is already up.
    unsafe {
        let res = initialize_Client_FetchExport(1, drorb_io_world());
        if drorb_io_ok(res) == 0 {
            panic!("initialize_Client_FetchExport returned an IO error");
        }
        drorb_obj_dec(res);
    }
}

/// Cross a `ByteArray -> ByteArray` client export with `input`, returning the
/// output bytes. Runtime-owner thread only.
fn cross(entry: unsafe extern "C" fn(*mut LeanObject) -> *mut LeanObject, input: &[u8]) -> Vec<u8> {
    // SAFETY: `entry` is a real `@[export]` symbol; the argument is a fresh
    // sarray the callee consumes, and the result is an owned sarray we copy then
    // release.
    unsafe {
        let arg = drorb_sarray_of_bytes(input.as_ptr(), input.len());
        let out = entry(arg);
        let n = drorb_sarray_len(out);
        let p = drorb_sarray_ptr(out);
        let v = std::slice::from_raw_parts(p, n).to_vec();
        drorb_obj_dec(out);
        v
    }
}

/// The parse of an upstream response by the verified client.
#[derive(Debug, Clone, PartialEq)]
pub struct ParsedResponse {
    /// The status code the verified parser decoded (via the proven decimal inverse).
    pub status: u16,
    /// The response body the verified parser split off.
    pub body: Vec<u8>,
}

/// Serialize a `GET`-style request line via the verified serializer:
/// `method SP target SP version CRLF CRLF` (no headers). Runtime-owner thread only.
pub fn verified_serialize_request(method: &[u8], target: &[u8], version: &[u8]) -> Vec<u8> {
    let mut framed = Vec::new();
    framed.push(method.len() as u8);
    framed.extend_from_slice(method);
    framed.push(target.len() as u8);
    framed.extend_from_slice(target);
    framed.push(version.len() as u8);
    framed.extend_from_slice(version);
    cross(drorb_request_serialize, &framed)
}

/// Parse an upstream response with the verified client parser. `None` on a parse
/// failure (the byte `0`); `Some` with the decoded status and body otherwise.
/// Runtime-owner thread only.
pub fn verified_parse_response(bytes: &[u8]) -> Option<ParsedResponse> {
    let out = cross(drorb_response_parse, bytes);
    match out.split_first() {
        Some((&1, rest)) => {
            // rest = <decimal status> 0 <body>
            let sep = rest.iter().position(|&b| b == 0)?;
            let status: u16 = std::str::from_utf8(&rest[..sep]).ok()?.parse().ok()?;
            Some(ParsedResponse {
                status,
                body: rest[sep + 1..].to_vec(),
            })
        }
        _ => None,
    }
}

/// Dial `addr`, write `request` verbatim, read the whole response, and parse it
/// with the verified client. The socket I/O is the host's; the request bytes and
/// the response parse are the proven client core. Runtime-owner thread only (the
/// verified parse crosses the Lean seam).
pub fn dial_and_parse(
    addr: SocketAddr,
    request: &[u8],
    timeout: Duration,
) -> std::io::Result<Option<ParsedResponse>> {
    let mut up = TcpStream::connect_timeout(&addr, timeout)?;
    up.set_nodelay(true).ok();
    up.set_read_timeout(Some(timeout)).ok();
    up.set_write_timeout(Some(timeout)).ok();
    up.write_all(request)?;
    up.flush()?;
    let mut buf = Vec::with_capacity(4096);
    up.read_to_end(&mut buf)?;
    Ok(verified_parse_response(&buf))
}

/// Serialize the proven HTTP/2 client submit octets for a bodyless `GET` on
/// `authority`/`path`: the client preface, an empty SETTINGS, and the HPACK
/// `HEADERS` frame (`Client.H2.requestBytes`). Runtime-owner thread only.
pub fn h2_verified_request(authority: &[u8], path: &[u8]) -> Vec<u8> {
    let mut framed = Vec::new();
    framed.push(authority.len() as u8);
    framed.extend_from_slice(authority);
    framed.push(path.len() as u8);
    framed.extend_from_slice(path);
    cross(drorb_h2_request, &framed)
}

/// Reassemble an upstream HTTP/2 response through the verified receive path
/// (`Client.H2Receive.feed` + real Huffman decode). `None` on a receive failure.
/// Runtime-owner thread only.
pub fn h2_verified_parse(bytes: &[u8]) -> Option<ParsedResponse> {
    let out = cross(drorb_h2_response, bytes);
    match out.split_first() {
        Some((&1, rest)) => {
            let sep = rest.iter().position(|&b| b == 0)?;
            let status: u16 = std::str::from_utf8(&rest[..sep]).ok()?.parse().ok()?;
            Some(ParsedResponse {
                status,
                body: rest[sep + 1..].to_vec(),
            })
        }
        _ => None,
    }
}

/// Dial `addr`, open an HTTP/2 (prior-knowledge / h2c) connection with the proven
/// client submit octets, read the response frame flight, and reassemble it with
/// the verified receive path. The socket I/O is the host's; the request octets and
/// the response reassembly are the proven `Client.H2` / `Client.H2Receive` core.
/// Runtime-owner thread only. (TLS+ALPN negotiation of `h2` is the front the caller
/// supplies; over a cleartext h2c upstream this is the whole exchange.)
pub fn h2_dial_and_parse(
    addr: SocketAddr,
    authority: &[u8],
    path: &[u8],
    timeout: Duration,
) -> std::io::Result<Option<ParsedResponse>> {
    let request = h2_verified_request(authority, path);
    let mut up = TcpStream::connect_timeout(&addr, timeout)?;
    up.set_nodelay(true).ok();
    up.set_read_timeout(Some(timeout)).ok();
    up.set_write_timeout(Some(timeout)).ok();
    up.write_all(&request)?;
    up.flush()?;
    let mut buf = Vec::with_capacity(4096);
    up.read_to_end(&mut buf)?;
    Ok(h2_verified_parse(&buf))
}
