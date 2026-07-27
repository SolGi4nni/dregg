//! `dregg-zkoracle-prove` — **the zkOracle PROVER**: the Rust realization that
//! PRODUCES and VERIFIES a zkOracle attestation over an Anthropic `POST /v1/messages`
//! session. It makes `metatheory/Dregg2/Crypto/ZkOracle.lean::zkOracle_sound` LIVE,
//! exactly as `deco-prove` made `Crypto/Deco` live — generalizing the DECO/tlsn machinery
//! from Stripe to the Anthropic API.
//!
//! An attestation certifies a request is simultaneously:
//!
//! ```text
//!   authentic   — a genuine TLS session with api.anthropic.com (tlsn/MPC-TLS), the
//!                 x-api-key REDACTED (prove the response without revealing the key);
//!   well-formed — the response body lies in a JSON context-free language, witnessed by a
//!                 producesChain parse certificate (Cfg.lean), nested structure a DFA cannot;
//!   injection-free — the user field UNMATCHES the handlebars template `.* {{ .*`, stated
//!                 as a match against the NATIVE VERIFIED COMPLEMENT `neg` (dregg-dfa).
//! ```
//!
//! [`verify_zkoracle`] is the 3-leg composition ([`attestation`]): all three must pass
//! to ACCEPT; a forged/tampered presentation, a malformed body, or a `{{`-bearing field
//! each independently REFUSE.
//!
//! ## What is real vs the operational remainder
//!
//! - **REAL (this crate, fully tested):** the CFG parse-certificate prover+verifier
//!   ([`cfg`]) over genuine JSON, the injection-free `neg`-complement matcher
//!   ([`injection`], backed by dregg-dfa's verified derivative `Re`), the authentic-leg
//!   tlsn adapter ([`authentic`]) with server/notary pinning + presentation-signature +
//!   api-key redaction, and their composition ([`attestation`]).
//! - **REAL in the `dregg-zkoracle-live` CRATE:** a genuine MPC-TLS 2PC roundtrip against a
//!   real HTTPS host — git-pinned TLSNotary, a separate hosted Notary + a Prover, a real
//!   `presentation.verify()`. It supplies leg 1 through [`attestation::MpcTlsLeg`].
//! - **Operational remainder (NAMED, not built):** pointing the Prover at the live
//!   `api.anthropic.com` with a real key + a deployed/pinned notary. See
//!   `docs/deos/ZKORACLE-PROVER-STATUS.md`.
//!
//! ## ⚑ THIS CRATE HAS NO CARGO FEATURES, ON PURPOSE
//!
//! The heavy `mpz` 2PC/garbling + tokio + rustls backend used to be a `tlsn-live` feature
//! here. A cargo feature UNIFIES across a workspace resolve, so an unrelated member
//! (`dregg-oracle`, whose `default` enabled it) decided whether THIS crate's live modules
//! compiled and whether ten of its tests existed: `cargo test -p dregg-zkoracle-prove` and
//! `cargo test --workspace` ran different suites over the same source. Worse, the
//! `verify_mpctls_leg` PROVENANCE GATE was a `#[cfg]`/`#[cfg(not)]` pair — real crypto or an
//! immediate refusal, chosen by the package selection.
//!
//! The backend is now a separate unconditional crate and leg 1 is an injected
//! [`attestation::MpcTlsLeg`] the caller names. This crate compiles identically under every
//! selection.

pub mod attestation;
pub mod authentic;
pub mod cfg;
pub mod endpoints;
pub mod injection;
pub mod render;
pub mod sigv4;
pub mod zk_leg;

pub use attestation::{
    AuthenticPolicy, AuthenticProvenance, MpcTlsLeg, NoMpcTlsBackend, ProveError, VerifiedZkOracle,
    ZkOracleAttestation, ZkOracleError, attestation_over_authenticated_body, authentic_provenance,
    prove_zkoracle, prove_zkoracle_with_stark, verify_legs_over_session, verify_zkoracle,
    verify_zkoracle_with_policy,
};
pub use authentic::{
    AnthropicConfig, AnthropicPresentation, AuthenticError, AuthenticSession, EndpointConfig,
    EndpointPresentation, EndpointSpec, FixtureNotary, SecretHeader, TlsnVerifyingKey,
    build_anthropic_fixture, build_endpoint_fixture, verify_anthropic_presentation,
    verify_endpoint_presentation,
};
pub use cfg::{
    CfgError, CompactCert, ParseCertificate, expand_compact, json_grammar, prove_cfg_cert,
    prove_cfg_compact, tokenize, verify_cfg_cert, verify_cfg_compact,
};
pub use endpoints::github::{
    GithubCommitFact, github_commit_spec, prove_github_commit, verify_github_commit,
};
pub use endpoints::price::{
    AttestedPrice, CoinbaseSpotOracle, PriceError, PriceOracle, coinbase_spot_spec,
    prove_coinbase_spot, verify_coinbase_spot,
};
pub use injection::{injection_free, injection_template};
pub use zk_leg::{
    ZkInjectionProof, ZkLegError, injection_dfa_table, prove_injection_leg, verify_injection_leg,
};
