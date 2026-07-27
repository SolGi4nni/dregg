//! **The LIVE half of the endpoint catalogue** — the same three web facts as
//! [`dregg_zkoracle_prove::endpoints`], proved over a REAL MPC-TLS 2PC session instead of a
//! fixture presentation.
//!
//! Each endpoint here does exactly two things the fixture path does not: it runs the genuine
//! roundtrip ([`crate::tlsn_live`]) and it authenticates leg 1 with real `tlsn` crypto
//! ([`crate::TlsnHostLeg`]). Everything else — building the attestation over the
//! authenticated body, and extracting + cross-checking the fact — is the SHARED code in
//! `dregg-zkoracle-prove`:
//!
//! - [`dregg_zkoracle_prove::attestation::attestation_over_authenticated_body`]
//! - [`dregg_zkoracle_prove::endpoints::price::price_fact_over_session`]
//! - [`dregg_zkoracle_prove::endpoints::github::commit_fact_over_session`]
//!
//! Those three used to be duplicated verbatim inside `#[cfg(feature = "tlsn-live")]` blocks,
//! which meant the live path's asset/sha cross-check was a COPY of the fixture path's and
//! nothing held the two copies together. They are now one function each, reached from both.

pub mod generic;
pub mod github;
pub mod price;
