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
//! - **REAL (default build, fully tested):** the CFG parse-certificate prover+verifier
//!   ([`cfg`]) over genuine JSON, the injection-free `neg`-complement matcher
//!   ([`injection`], backed by dregg-dfa's verified derivative `Re`), the authentic-leg
//!   tlsn adapter ([`authentic`]) with server/notary pinning + presentation-signature +
//!   api-key redaction, and their composition ([`attestation`]).
//! - **REAL behind `tlsn-live`:** a genuine local MPC-TLS 2PC roundtrip against an
//!   Anthropic-shaped HTTPS endpoint ([`tlsn_live`]) — vendored TLSNotary, a real Notary +
//!   Prover, `presentation.verify()`. The heavy `mpz`/tokio/rustls backend, gated so the
//!   default build stays light.
//! - **Operational remainder (NAMED, not built):** pointing the Prover at the live
//!   `api.anthropic.com` with a real key + a deployed/pinned notary. See
//!   `docs/deos/ZKORACLE-PROVER-STATUS.md`.

pub mod attestation;
pub mod authentic;
pub mod cfg;
pub mod injection;
#[cfg(feature = "tlsn-live")]
pub mod tlsn_live;

pub use attestation::{
    ProveError, VerifiedZkOracle, ZkOracleAttestation, ZkOracleError, prove_zkoracle,
    verify_zkoracle,
};
pub use authentic::{
    AnthropicConfig, AnthropicPresentation, AuthenticError, AuthenticSession, FixtureNotary,
    TlsnVerifyingKey, build_anthropic_fixture, verify_anthropic_presentation,
};
pub use cfg::{
    CfgError, CompactCert, ParseCertificate, expand_compact, json_grammar, prove_cfg_cert,
    prove_cfg_compact, tokenize, verify_cfg_cert, verify_cfg_compact,
};
pub use injection::{injection_free, injection_template};
