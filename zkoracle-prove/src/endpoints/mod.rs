//! **The endpoint catalogue** — the GENERALITY proof: zkOracle verifies any web fact.
//!
//! The authentic + well-formed + injection-free machinery ([`crate::attestation`]) is
//! endpoint-agnostic; an [`crate::authentic::EndpointSpec`] (host / method / secret header)
//! plus a per-endpoint response SCHEMA turns it into a specific verified-web-oracle. The
//! original Anthropic `POST /v1/messages` oracle is one such endpoint; this module adds two
//! more, each proving a PUBLIC web fact trustlessly:
//!
//! - [`github`] — `GET api.github.com/repos/{owner}/{repo}/commits/{sha}`: the commit
//!   exists, by `{author}`, at `{date}`, with `{message}`. No auth (public), read-only, so
//!   the injection-free leg is **n/a** (there is no user-supplied field); the teeth are
//!   authentic (the GitHub TLS session) ∧ well-formed (the response JSON, real CFG cert) ∧
//!   the cross-leg weld to ONE response, plus a request/response `sha` cross-check.
//! - [`price`] — `GET api.coinbase.com/v2/prices/{asset}/spot`: `{asset}` quoted at
//!   `{amount}` at `{time}` (the session time). Ships a clean [`price::PriceOracle`]
//!   interface the downstream auditable-fund lane consumes: `price(asset) -> AttestedPrice`.
//!
//! ## What is real vs the live-endpoint remainder
//!
//! Same honest boundary as the Anthropic endpoint: the default build exercises each oracle
//! over a fixture presentation (the modeled tlsn notary + a realistic transcript); the real
//! local MPC-TLS 2PC roundtrip is the `tlsn-live` path ([`crate::tlsn_live`]). Pointing the
//! Prover at the live `api.github.com` / `api.coinbase.com` (a real TLS session + a
//! deployed/pinned notary) is the NAMED operational remainder — see
//! `docs/deos/ZKORACLE-ENDPOINTS.md`.

pub mod github;
pub mod price;

/// The HTTP request target (the path) out of the authenticated request bytes: the second
/// whitespace-delimited field of the request line `METHOD <target> HTTP/1.1`. The request
/// line is part of the notary-signed presentation, so the target is authenticated.
pub(crate) fn request_target(sent: &[u8]) -> Option<String> {
    let line_end = sent
        .windows(2)
        .position(|w| w == b"\r\n")
        .unwrap_or(sent.len());
    let line = &sent[..line_end];
    let mut fields = line.split(|&b| b == b' ').filter(|f| !f.is_empty());
    let _method = fields.next()?;
    let target = fields.next()?;
    Some(String::from_utf8_lossy(target).into_owned())
}
