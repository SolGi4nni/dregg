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
//! ## What is here vs what is in `dregg-zkoracle-live`
//!
//! This module is the ENDPOINT-AGNOSTIC half: the spec, the response schema, and the
//! fact-extractor that runs over an ALREADY-AUTHENTICATED session
//! ([`price::price_fact_over_session`], [`github::commit_fact_over_session`]). The default
//! build exercises each oracle over a fixture presentation (the modeled tlsn notary + a
//! realistic transcript).
//!
//! The real MPC-TLS 2PC roundtrip against the live host, and the third `generic` endpoint
//! (which has no fixture path at all), live in the `dregg-zkoracle-live` CRATE. They call the
//! same extractors above, so both paths cross-check the same way. Pointing the Prover at a
//! deployed/pinned notary is the NAMED operational remainder — see
//! `docs/deos/ZKORACLE-ENDPOINTS.md`.

pub mod github;
pub mod price;

/// The HTTP request target (the path) out of the authenticated request bytes: the second
/// whitespace-delimited field of the request line `METHOD <target> HTTP/1.1`. The request
/// line is part of the notary-signed presentation, so the target is authenticated.
///
/// `pub` (not `pub(crate)`) because `dregg-zkoracle-live`'s endpoint provers read the target
/// out of the same authenticated request line after a real 2PC session.
pub fn request_target(sent: &[u8]) -> Option<String> {
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
