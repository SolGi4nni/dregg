//! `dregg-tee-produce` — the TEE attestation **producer** scaffold.
//!
//! The verify side of the TEE fact rail is done: `dregg-tee-verify` checks a real
//! AWS Nitro attestation document (COSE sig + X.509 chain to the pinned AWS root)
//! and `dregg_cell::tee_attest` re-checks its claims against the landed
//! [`grain_turn::ATTESTATION_SLOT`] commitment. This crate is the missing half:
//! **getting a vendor-signed document out of the enclave with the caller's 32-byte
//! turn/session commitment bound into `report_data`.**
//!
//! ## The binding convention (the whole point)
//!
//! The host computes the 32-byte commitment it is about to bind at the grain
//! turn-cell's attestation slot (`AgentPlatform::drive_serving_attested`), sends it
//! to the enclave as [`QuoteRequest::report_data`], and the enclave asks its
//! hardware for a quote binding EXACTLY those bytes (Nitro: `user_data`). The
//! verify rail then requires `quote.report_data == landed slot value` — so a quote
//! is bound to one specific session, and a replayed quote for a different session
//! is refused by the predicate, not by policy prose. Freshness beyond that binding
//! is the caller's job: put a nonce in what the commitment commits to.
//!
//! ## Transport
//!
//! One newline-delimited JSON frame per message over ANY byte stream — a vsock
//! socket (the real Nitro host↔enclave channel), TCP, or an in-process pipe —
//! mirroring `grain-jail`'s `LineChannel` philosophy: generic over `Read + Write`,
//! a hard per-line byte cap so a hostile peer cannot OOM the other side, and JSON
//! frames so the wire is debuggable. Binary payloads (the 32-byte commitment, the
//! CBOR/COSE document) ride as lowercase hex.
//!
//! ## Backends (all honest)
//!
//! - [`NitroNsmBackend`] (`nitro` feature): the REAL NSM `GetAttestationDoc` ioctl
//!   via `aws-nitro-enclaves-nsm-api`. Works only inside a running Nitro Enclave;
//!   everywhere else `/dev/nsm` is absent and it returns `Err` (fail-closed).
//! - [`FixtureBackend`] (`fixture-backend` feature): NOT an attestation producer —
//!   a transport/wiring test aid that serves the one REAL captured live-enclave
//!   document, and only for the exact `report_data` that enclave actually bound.
//! - There is deliberately no mock/self-signed backend. A backend that cannot
//!   reach real hardware returns `Err`; it never fabricates a document.

use std::io::{BufRead, BufReader, Read, Write};

use serde::{Deserialize, Serialize};

#[cfg(feature = "fixture-backend")]
pub mod fixture;
#[cfg(feature = "nitro")]
pub mod nsm;

#[cfg(feature = "fixture-backend")]
pub use fixture::{FIXTURE_REPORT_DATA, FixtureBackend};
#[cfg(feature = "nitro")]
pub use nsm::NitroNsmBackend;

/// A request for one attestation quote: the exact 32 bytes the enclave must bind
/// into the quote's `report_data` (Nitro: the attestation document's `user_data`).
/// This is the turn/session commitment the host is about to witness at the grain
/// turn-cell's attestation slot — the verify rail's binding contract
/// (`dregg_cell::tee_attest::TeeReportClaims::report_data`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuoteRequest {
    /// The 32-byte commitment to bind. Exactly these bytes must come back in the
    /// verified quote's `report_data`, or the predicate refuses the quote.
    pub report_data: [u8; 32],
}

/// A produced quote: the raw vendor-signed attestation document bytes (Nitro: the
/// CBOR/COSE_Sign1 blob the NSM signed). Opaque to this crate — authentication is
/// entirely `dregg-tee-verify`'s job; the producer only transports it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuoteResponse {
    /// The vendor-signed attestation document, verbatim.
    pub document: Vec<u8>,
}

/// A quote source the enclave-side server answers requests from. Implementations
/// MUST be honest: return a REAL vendor-signed document binding exactly the
/// requested `report_data`, or `Err`. Returning fabricated bytes as if they were
/// an attestation is a soundness bug (the verify rail would refuse them anyway —
/// no chain to the pinned root — but the producer must not lie either).
pub trait QuoteBackend {
    /// Produce a vendor-signed attestation document binding `report_data`.
    fn attestation_document(&self, report_data: [u8; 32]) -> Result<Vec<u8>, String>;
}

/// Per-frame byte cap, both directions (a real Nitro doc is ~5 KiB; hex doubles
/// it; 1 MiB leaves generous headroom while keeping a flood bounded).
pub const MAX_FRAME_BYTES: usize = 1 << 20;

/// Errors the host-side client surfaces. Everything is fail-closed: a transport
/// or protocol failure yields no document.
#[derive(Debug)]
pub enum QuoteError {
    /// The stream failed (broken pipe, EOF before a response, flood cap hit).
    Transport(String),
    /// The peer answered with a well-formed refusal (the backend said `Err`).
    Refused(String),
    /// The peer's bytes were not a well-formed response frame.
    Protocol(String),
}

impl std::fmt::Display for QuoteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuoteError::Transport(e) => write!(f, "quote transport failed: {e}"),
            QuoteError::Refused(e) => write!(f, "quote refused by the enclave: {e}"),
            QuoteError::Protocol(e) => write!(f, "quote protocol violation: {e}"),
        }
    }
}

impl std::error::Error for QuoteError {}

/// The request frame: `{"report_data":"<64 hex chars>"}`.
#[derive(Serialize, Deserialize)]
struct WireRequest {
    report_data: String,
}

/// The response frame: `{"document":"<hex>"}` on success, `{"error":"…"}` on a
/// refusal. Exactly one of the two fields is present.
#[derive(Serialize, Deserialize)]
struct WireResponse {
    #[serde(skip_serializing_if = "Option::is_none")]
    document: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
}

/// Read one newline-terminated frame with the [`MAX_FRAME_BYTES`] flood cap
/// (mirrors `grain_jail::LineChannel::recv`). `Ok(None)` on clean EOF.
fn read_frame<R: BufRead>(reader: &mut R) -> Result<Option<String>, String> {
    let mut line = String::new();
    let n = reader
        .take(MAX_FRAME_BYTES as u64 + 1)
        .read_line(&mut line)
        .map_err(|e| format!("read frame: {e}"))?;
    if n == 0 {
        return Ok(None); // clean EOF — the peer closed.
    }
    if line.len() > MAX_FRAME_BYTES && !line.ends_with('\n') {
        return Err("frame exceeds the max frame length (flood)".to_string());
    }
    Ok(Some(line.trim_end_matches(['\n', '\r']).to_string()))
}

fn decode_report_data(hex_rd: &str) -> Result<[u8; 32], String> {
    let bytes = hex::decode(hex_rd).map_err(|e| format!("report_data hex: {e}"))?;
    if bytes.len() != 32 {
        return Err(format!("report_data must be 32 bytes, got {}", bytes.len()));
    }
    let mut rd = [0u8; 32];
    rd.copy_from_slice(&bytes);
    Ok(rd)
}

// ─────────────────────────────────────────────────────────────────────
// Enclave side — the quote server.
// ─────────────────────────────────────────────────────────────────────

/// Serve quote requests from `reader`/`writer` (the enclave's end of the vsock /
/// stream) until the peer closes. Each request frame is answered with exactly one
/// response frame; a backend refusal or a malformed request becomes an `error`
/// frame (the connection stays up — per-request failures are the peer's to see),
/// while a transport failure ends the loop. Returns how many quotes were served
/// successfully.
pub fn serve_quotes<R: Read, W: Write>(
    reader: R,
    mut writer: W,
    backend: &dyn QuoteBackend,
) -> Result<u64, QuoteError> {
    let mut reader = BufReader::new(reader);
    let mut served = 0u64;
    loop {
        let frame = match read_frame(&mut reader).map_err(QuoteError::Transport)? {
            None => return Ok(served),
            Some(f) if f.is_empty() => continue, // blank keep-alive line
            Some(f) => f,
        };
        let response = match serde_json::from_str::<WireRequest>(&frame)
            .map_err(|e| format!("request frame: {e}"))
            .and_then(|req| decode_report_data(&req.report_data))
            .and_then(|rd| backend.attestation_document(rd))
        {
            Ok(document) => {
                served += 1;
                WireResponse {
                    document: Some(hex::encode(document)),
                    error: None,
                }
            }
            Err(e) => WireResponse {
                document: None,
                error: Some(e),
            },
        };
        let mut out = serde_json::to_string(&response)
            .map_err(|e| QuoteError::Protocol(format!("encode response: {e}")))?;
        out.push('\n');
        writer
            .write_all(out.as_bytes())
            .and_then(|_| writer.flush())
            .map_err(|e| QuoteError::Transport(format!("write response: {e}")))?;
    }
}

// ─────────────────────────────────────────────────────────────────────
// Host side — the quote client.
// ─────────────────────────────────────────────────────────────────────

/// Request one quote over a bidirectional `stream` (vsock/TCP/pipe): send the
/// request frame binding `report_data`, read the one response frame, return the
/// raw vendor-signed document bytes. Fail-closed on refusal, EOF, flood, or a
/// malformed frame. The caller hands the document to `dregg-tee-verify` (or to
/// the registered `dregg_cell::tee_attest` rail) — this function does NOT
/// authenticate it.
pub fn request_quote<S: Read + Write>(
    stream: &mut S,
    report_data: [u8; 32],
) -> Result<Vec<u8>, QuoteError> {
    let request = WireRequest {
        report_data: hex::encode(report_data),
    };
    let mut out = serde_json::to_string(&request)
        .map_err(|e| QuoteError::Protocol(format!("encode request: {e}")))?;
    out.push('\n');
    stream
        .write_all(out.as_bytes())
        .and_then(|_| stream.flush())
        .map_err(|e| QuoteError::Transport(format!("write request: {e}")))?;

    let mut reader = BufReader::new(stream);
    let frame = read_frame(&mut reader)
        .map_err(QuoteError::Transport)?
        .ok_or_else(|| QuoteError::Transport("EOF before a response frame".to_string()))?;
    let response: WireResponse = serde_json::from_str(&frame)
        .map_err(|e| QuoteError::Protocol(format!("response frame: {e}")))?;
    if let Some(error) = response.error {
        return Err(QuoteError::Refused(error));
    }
    let document_hex = response.document.ok_or_else(|| {
        QuoteError::Protocol("response carries neither document nor error".into())
    })?;
    let document = hex::decode(&document_hex)
        .map_err(|e| QuoteError::Protocol(format!("document hex: {e}")))?;
    if document.is_empty() {
        return Err(QuoteError::Protocol("empty attestation document".into()));
    }
    Ok(document)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A backend that always refuses — the shape every non-hardware path must
    /// take (fail-closed `Err`, never a fabricated document).
    struct RefuseBackend;
    impl QuoteBackend for RefuseBackend {
        fn attestation_document(&self, _rd: [u8; 32]) -> Result<Vec<u8>, String> {
            Err("no attestation hardware reachable (fail-closed)".to_string())
        }
    }

    #[test]
    fn a_refusing_backend_yields_a_refused_error_not_a_document() {
        let mut request_wire = Vec::new();
        // Client half 1: emit the request into a buffer.
        {
            struct WOnly<'a>(&'a mut Vec<u8>);
            impl Read for WOnly<'_> {
                fn read(&mut self, _b: &mut [u8]) -> std::io::Result<usize> {
                    Ok(0)
                }
            }
            impl Write for WOnly<'_> {
                fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
                    self.0.write(b)
                }
                fn flush(&mut self) -> std::io::Result<()> {
                    Ok(())
                }
            }
            let mut half = WOnly(&mut request_wire);
            // EOF after the (refusal) response would be needed; here we only
            // check the server leg, so drive it directly below instead.
            let _ = request_quote(&mut half, [7u8; 32]);
        }
        // Server: consume the emitted request, answer with the refusal frame.
        let mut response_wire = Vec::new();
        let served = serve_quotes(request_wire.as_slice(), &mut response_wire, &RefuseBackend)
            .expect("the server survives a per-request refusal");
        assert_eq!(served, 0, "a refusal is not a served quote");
        let frame = String::from_utf8(response_wire).unwrap();
        let resp: WireResponse = serde_json::from_str(frame.trim_end()).unwrap();
        assert!(resp.document.is_none(), "no document is ever fabricated");
        assert!(resp.error.unwrap().contains("fail-closed"));
    }

    #[test]
    fn a_malformed_request_frame_is_answered_with_an_error_frame() {
        let mut out = Vec::new();
        let served = serve_quotes(
            b"{\"report_data\":\"abcd\"}\nnot json at all\n".as_slice(),
            &mut out,
            &RefuseBackend,
        )
        .expect("malformed requests do not kill the server");
        assert_eq!(served, 0);
        let frames: Vec<&str> = std::str::from_utf8(&out)
            .unwrap()
            .trim_end()
            .lines()
            .collect();
        assert_eq!(
            frames.len(),
            2,
            "every request frame gets exactly one answer"
        );
        for f in frames {
            let resp: WireResponse = serde_json::from_str(f).unwrap();
            assert!(resp.document.is_none());
            assert!(resp.error.is_some());
        }
    }

    #[test]
    fn a_flooding_peer_is_cut_off_not_buffered_unboundedly() {
        // A "line" larger than the cap with no newline: the server must error out,
        // not allocate without bound.
        let flood = vec![b'a'; MAX_FRAME_BYTES + 10];
        let mut out = Vec::new();
        let err = serve_quotes(flood.as_slice(), &mut out, &RefuseBackend).unwrap_err();
        assert!(matches!(err, QuoteError::Transport(_)));
    }

    #[test]
    fn the_client_refuses_a_response_with_neither_document_nor_error() {
        struct Fixed<'a> {
            response: &'a [u8],
            sink: Vec<u8>,
        }
        impl Read for Fixed<'_> {
            fn read(&mut self, b: &mut [u8]) -> std::io::Result<usize> {
                self.response.read(b)
            }
        }
        impl Write for Fixed<'_> {
            fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
                self.sink.write(b)
            }
            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        let mut s = Fixed {
            response: b"{}\n",
            sink: Vec::new(),
        };
        assert!(matches!(
            request_quote(&mut s, [1u8; 32]),
            Err(QuoteError::Protocol(_))
        ));
        // And a refusal frame surfaces as Refused, never as bytes.
        let mut s = Fixed {
            response: b"{\"error\":\"nope\"}\n",
            sink: Vec::new(),
        };
        assert!(matches!(
            request_quote(&mut s, [1u8; 32]),
            Err(QuoteError::Refused(e)) if e == "nope"
        ));
    }
}
