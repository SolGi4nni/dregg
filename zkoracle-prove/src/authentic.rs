//! **The authentic leg** — the tlsn / MPC-TLS (DECO/zkTLS) attestation of an Anthropic
//! `POST /v1/messages` session, generalized from deco-prove's Stripe adapter.
//!
//! This is the Rust realization of `zkOracle_sound`'s **authentic** conjunct
//! (`∃ w, DecoRelation … decoStmt w`): a verified tlsn presentation certifies that the
//! disclosed response body came from a genuine TLS session with the pinned Anthropic host,
//! with the **`x-api-key` secret REDACTED** — the killer property: prove what the model
//! returned WITHOUT revealing your Anthropic API key.
//!
//! ## What this module is (honest scope)
//!
//! This is the **Layer-2 tlsn-attestation INTERFACE + ADAPTER** (the exact shape of
//! deco-prove's `tlsn_attest.rs`, generalized Stripe→Anthropic), exercised end-to-end by
//! an in-tree fixture. The genuine live MPC-TLS 2PC run lives behind the `tlsn-live`
//! feature ([`crate::tlsn_live`]) — vendored TLSNotary, a real Notary + Prover, a real
//! `presentation.verify()`. The operational remainder — pointing the Prover at the live
//! `api.anthropic.com` with a real key + a deployed notary — is NAMED, not faked
//! (`docs/deos/ZKORACLE-PROVER-STATUS.md`).
//!
//! The modeled notary signature curve is **ed25519** (the curve already in-tree, as in
//! deco-prove); tlsn's real notary signs secp256k1/p256 — a notary-config detail, not a
//! semantic one.

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};

/// The pinned Anthropic API host a genuine messages presentation must be a session with.
pub const ANTHROPIC_SERVER_NAME: &str = "api.anthropic.com";

/// The Anthropic messages endpoint path.
pub const MESSAGES_PATH: &str = "/v1/messages";

/// The request header carrying the Anthropic secret key — the value that MUST be redacted
/// (never authenticated) in the presentation.
pub const API_KEY_HEADER: &str = "x-api-key";

/// An obvious placeholder secret so no real-key SHAPE lands in the tree; the redaction is
/// identical regardless of the token's contents.
pub const API_KEY_PLACEHOLDER: &str = "sk-ant-MERCHANT-API-KEY-PLACEHOLDER";

/// Domain separation over the modeled notary signature.
const TLSN_PRESENTATION_DOMAIN: &[u8] = b"dregg/zkoracle/tlsn-presentation/v1";

// ─────────────────────────────────────────────────────────────────────────────
// The ENDPOINT SPECIFICATION — the DATA that turns the generic prover into a specific
// verified-web-oracle. A new endpoint (GitHub commit, a price quote, …) is an
// [`EndpointSpec`] + a response schema, NOT a fork of the prover: the authentic-leg
// verifier ([`verify_endpoint_presentation`]) and the fixture builder
// ([`build_endpoint_fixture`]) are endpoint-agnostic and driven entirely by the spec.
// ─────────────────────────────────────────────────────────────────────────────

/// A secret request header whose VALUE is redacted (never authenticated) in the
/// presentation — the "prove the response without revealing your key" property. Present
/// for authed endpoints (Anthropic's `x-api-key`); ABSENT for public read-only endpoints
/// (a public GitHub commit, a public price quote — nothing to hide).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecretHeader {
    /// The header name (e.g. `x-api-key`, `authorization`).
    pub name: String,
    /// The placeholder value the fixture sends (an obvious non-secret, so no real-key
    /// SHAPE lands in the tree; redaction is identical regardless of the token's contents).
    pub placeholder: String,
    /// A marker substring that must NEVER survive into the authenticated request bytes
    /// (defense in depth — refuse even a partial leak).
    pub marker: String,
}

/// **`EndpointSpec`** — the endpoint-specific configuration, factored out so a new web
/// fact is DATA. It pins the transport identity + shape:
///
/// - `server_name` — the TLS host the session must be pinned to (`api.anthropic.com`,
///   `api.github.com`, `api.coinbase.com`);
/// - `method` — the HTTP method the request line carries (`POST`, `GET`);
/// - `secret_header` — the redacted secret header, if any (`None` = a public endpoint).
///
/// The *response schema* (the typed fact a body parses into) lives with each endpoint
/// module ([`crate::endpoints`]); this spec is the transport contract the authentic leg
/// enforces uniformly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EndpointSpec {
    /// A short identifier for the endpoint (`anthropic-messages`, `github-commit`,
    /// `coinbase-spot`) — labels the oracle, surfaces in diagnostics.
    pub id: String,
    /// The TLS host a genuine presentation must be a session with.
    pub server_name: String,
    /// The HTTP method the fixture's request line carries.
    pub method: String,
    /// The redacted secret request header, or `None` for a public read-only endpoint.
    pub secret_header: Option<SecretHeader>,
}

impl EndpointSpec {
    /// The Anthropic `POST /v1/messages` oracle — the original endpoint, now expressed as
    /// data: pin `api.anthropic.com`, redact `x-api-key`.
    pub fn anthropic_messages() -> Self {
        EndpointSpec {
            id: "anthropic-messages".to_string(),
            server_name: ANTHROPIC_SERVER_NAME.to_string(),
            method: "POST".to_string(),
            secret_header: Some(SecretHeader {
                name: API_KEY_HEADER.to_string(),
                placeholder: API_KEY_PLACEHOLDER.to_string(),
                marker: "MERCHANT-API-KEY".to_string(),
            }),
        }
    }
}

/// **`EndpointConfig`** — an [`EndpointSpec`] plus the pinned notary anchor: everything the
/// authentic leg checks a presentation against. This is the canonical config the whole
/// prover/verifier (`prove_zkoracle`/`verify_zkoracle`) takes; [`AnthropicConfig`] is the
/// Anthropic-specialized constructor over it.
#[derive(Clone, Debug)]
pub struct EndpointConfig {
    /// The endpoint specification (host/method/secret-header).
    pub spec: EndpointSpec,
    /// The pinned notary verifying key anchor.
    pub expected_notary: TlsnVerifyingKey,
}

impl EndpointConfig {
    /// Pin an endpoint spec + a notary anchor.
    pub fn new(spec: EndpointSpec, expected_notary: TlsnVerifyingKey) -> Self {
        EndpointConfig {
            spec,
            expected_notary,
        }
    }

    /// The pinned server host.
    pub fn expected_server(&self) -> &str {
        &self.spec.server_name
    }
}

/// The notary's verifying key — models `tlsn_core::signing::VerifyingKey { alg, data }`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TlsnVerifyingKey {
    /// The signature algorithm identifier (modeled: `"ed25519"`).
    pub alg: String,
    /// The public key bytes (ed25519: 32 bytes).
    pub data: Vec<u8>,
}

/// A **verified tlsn presentation** over an Anthropic messages session — models the object
/// `tlsn_core` `presentation.verify(&provider)` yields.
///
/// The request direction discloses the target + non-secret headers but REDACTS the
/// `x-api-key` value (fill `X`, not authenticated). The response direction discloses the
/// full messages JSON body — the public evidence the well-formed (CFG) and injection-free
/// legs run over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EndpointPresentation {
    /// The notary's verifying key (a verifier pins its own anchor).
    pub verifying_key: TlsnVerifyingKey,
    /// The authenticated server identity (must be [`ANTHROPIC_SERVER_NAME`]).
    pub server_name: String,
    /// The session time (`connection_info.time`, unix seconds).
    pub connection_time: u64,
    /// The request-direction bytes as delivered (`sent_unsafe()`) — the `x-api-key` value
    /// positions are the fill byte `X`.
    pub sent: Vec<u8>,
    /// The response-direction bytes as delivered (`received_unsafe()`) — headers + the
    /// authenticated messages JSON body.
    pub recv: Vec<u8>,
    /// The notary's ed25519 signature over [`Self::canonical_signing_bytes`].
    pub notary_sig: [u8; 64],
}

impl EndpointPresentation {
    /// The canonical bytes the notary signs: domain + pinned identity + BOTH directions'
    /// delivered bytes. Tampering any disclosed byte breaks the signature.
    fn canonical_signing_bytes(&self) -> Vec<u8> {
        let mut m = Vec::new();
        m.extend_from_slice(TLSN_PRESENTATION_DOMAIN);
        m.extend_from_slice(&(self.server_name.len() as u64).to_le_bytes());
        m.extend_from_slice(self.server_name.as_bytes());
        m.extend_from_slice(&self.connection_time.to_le_bytes());
        m.extend_from_slice(&(self.sent.len() as u64).to_le_bytes());
        m.extend_from_slice(&self.sent);
        m.extend_from_slice(&(self.recv.len() as u64).to_le_bytes());
        m.extend_from_slice(&self.recv);
        m
    }
}

/// A verified tlsn presentation, endpoint-agnostic — the original `AnthropicPresentation`
/// name, kept as an alias since every endpoint (Anthropic, GitHub, price) shares the same
/// presentation shape (server identity + both directions' delivered bytes + notary sig).
pub type AnthropicPresentation = EndpointPresentation;

/// **`AnthropicConfig`** — the Anthropic-specialized [`EndpointConfig`] constructor, kept
/// for back-compat. It is a thin newtype that `Deref`s to [`EndpointConfig`], so it flows
/// into the generic `prove_zkoracle`/`verify_zkoracle` unchanged while a GitHub or price
/// oracle builds its own `EndpointConfig` directly.
#[derive(Clone, Debug)]
pub struct AnthropicConfig(pub EndpointConfig);

impl AnthropicConfig {
    /// Pin the Anthropic `POST /v1/messages` endpoint + a notary anchor.
    pub fn new(expected_notary: TlsnVerifyingKey) -> Self {
        AnthropicConfig(EndpointConfig::new(
            EndpointSpec::anthropic_messages(),
            expected_notary,
        ))
    }
}

impl core::ops::Deref for AnthropicConfig {
    type Target = EndpointConfig;
    fn deref(&self) -> &EndpointConfig {
        &self.0
    }
}

/// A verified authentic Anthropic session — the response body extracted from the
/// AUTHENTICATED transcript, with the api-key hidden.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticSession {
    /// The authenticated server identity.
    pub server_name: String,
    /// The session time.
    pub connection_time: u64,
    /// The authenticated messages JSON response body (the public evidence).
    pub response_body: Vec<u8>,
}

/// Why a presentation is refused by the adapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthenticError {
    /// The authenticated server is not the pinned Anthropic host.
    WrongServer { got: String },
    /// The presentation's verifying key is not the pinned notary anchor.
    WrongNotary,
    /// The notary key bytes are not a valid ed25519 point.
    MalformedKey,
    /// The notary signature does not verify (models a failed `presentation.verify()` —
    /// the transcript or identity was tampered).
    BadNotarySignature,
    /// The `x-api-key` secret survived into the authenticated request bytes — selective
    /// disclosure FAILED, the killer property is violated, refuse.
    ApiKeyDisclosed,
    /// The response direction has no HTTP header/body separator (`\r\n\r\n`).
    NoResponseBody,
}

impl core::fmt::Display for AuthenticError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AuthenticError::WrongServer { got } => {
                write!(
                    f,
                    "presentation server {got:?} is not the pinned {ANTHROPIC_SERVER_NAME:?}"
                )
            }
            AuthenticError::WrongNotary => {
                write!(f, "presentation notary key is not the pinned anchor")
            }
            AuthenticError::MalformedKey => {
                write!(f, "notary key bytes are not a valid ed25519 point")
            }
            AuthenticError::BadNotarySignature => {
                write!(f, "notary signature does not verify over the presentation")
            }
            AuthenticError::ApiKeyDisclosed => {
                write!(
                    f,
                    "the x-api-key secret was not redacted (selective disclosure failed)"
                )
            }
            AuthenticError::NoResponseBody => write!(f, "no header/body separator in the response"),
        }
    }
}

impl std::error::Error for AuthenticError {}

/// **THE ADAPTER** — verify a tlsn presentation of ANY endpoint session (the generalized
/// authentic leg) and extract the authenticated response body.
///
/// Enforces, in order, driven entirely by [`EndpointConfig`]/[`EndpointSpec`]: server
/// pinning (`spec.server_name`), notary pinning, the presentation signature, and — when
/// the spec declares a secret header — its redaction (the secret value must NOT appear in
/// the authenticated request bytes). A public read-only endpoint (`secret_header = None`)
/// skips the redaction step (there is nothing to hide). On success returns the
/// authenticated response body for the downstream legs.
///
/// ⚑ This checks the presentation as *delivered + signed*; the 2PC session-integrity that
/// makes the signature *trustless* is the named remaining wiring ([`crate::tlsn_live`] +
/// module docs).
pub fn verify_endpoint_presentation(
    pres: &EndpointPresentation,
    config: &EndpointConfig,
) -> Result<AuthenticSession, AuthenticError> {
    // (1) server pinning.
    if pres.server_name != config.spec.server_name {
        return Err(AuthenticError::WrongServer {
            got: pres.server_name.clone(),
        });
    }
    // (2) notary pinning.
    if pres.verifying_key != config.expected_notary {
        return Err(AuthenticError::WrongNotary);
    }
    // (3) the presentation signature (models presentation.verify()'s signature leg).
    let key_bytes: [u8; 32] = pres
        .verifying_key
        .data
        .as_slice()
        .try_into()
        .map_err(|_| AuthenticError::MalformedKey)?;
    let vk = VerifyingKey::from_bytes(&key_bytes).map_err(|_| AuthenticError::MalformedKey)?;
    let sig = Signature::from_bytes(&pres.notary_sig);
    vk.verify(&pres.canonical_signing_bytes(), &sig)
        .map_err(|_| AuthenticError::BadNotarySignature)?;

    // (4) selective disclosure — spec-driven. If the endpoint declares a secret header,
    // its placeholder/marker must NOT survive into the authenticated request bytes. A
    // public endpoint has no secret, so this step is n/a.
    if let Some(secret) = &config.spec.secret_header {
        if contains_subslice(&pres.sent, secret.placeholder.as_bytes())
            || contains_subslice(&pres.sent, secret.marker.as_bytes())
        {
            return Err(AuthenticError::ApiKeyDisclosed);
        }
    }

    // (5) extract the authenticated response body.
    let sep = find_subslice(&pres.recv, b"\r\n\r\n").ok_or(AuthenticError::NoResponseBody)?;
    let response_body = pres.recv[sep + 4..].to_vec();

    Ok(AuthenticSession {
        server_name: pres.server_name.clone(),
        connection_time: pres.connection_time,
        response_body,
    })
}

/// Back-compat alias for [`verify_endpoint_presentation`] (the Anthropic-named entry the
/// original call sites use; the config `Deref`s from [`AnthropicConfig`]).
pub fn verify_anthropic_presentation(
    pres: &EndpointPresentation,
    config: &EndpointConfig,
) -> Result<AuthenticSession, AuthenticError> {
    verify_endpoint_presentation(pres, config)
}

// ─────────────────────────────────────────────────────────────────────────────
// The fixture producer — models the tlsn notary + 2PC + live Anthropic session.
//
// ⚑ NOT a real notary. The in-tree PRODUCER that builds a tlsn-format presentation over a
// realistic Anthropic messages transcript so the adapter can be exercised end-to-end (and
// forgeries refuted) without the mpz 2PC stack. The genuine run is [`crate::tlsn_live`].
// ─────────────────────────────────────────────────────────────────────────────

/// The modeled notary that signs an [`EndpointPresentation`]. Deterministic from a seed.
pub struct FixtureNotary {
    signing: SigningKey,
}

impl FixtureNotary {
    /// A fixture notary from a 32-byte seed.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        FixtureNotary {
            signing: SigningKey::from_bytes(seed),
        }
    }

    /// The notary's pinnable verifying key.
    pub fn verifying_key(&self) -> TlsnVerifyingKey {
        TlsnVerifyingKey {
            alg: "ed25519".to_string(),
            data: self.signing.verifying_key().to_bytes().to_vec(),
        }
    }

    /// Sign a presentation (fills [`EndpointPresentation::notary_sig`]).
    pub fn sign(&self, mut pres: EndpointPresentation) -> EndpointPresentation {
        let sig: Signature = self.signing.sign(&pres.canonical_signing_bytes());
        pres.notary_sig = sig.to_bytes();
        pres
    }
}

/// **Build an Anthropic messages presentation fixture.**
///
/// Constructs a realistic authenticated HTTP/1.1 transcript of
/// `POST https://api.anthropic.com/v1/messages`:
///
/// - **Request (`sent`):** the request line + `host` + `x-api-key: sk-ant-…` + headers.
///   The `x-api-key` VALUE is REDACTED (fill `X`, NOT authenticated) — the killer use
///   case: prove the response WITHOUT revealing your Anthropic key.
/// - **Response (`recv`):** the status line + headers + the messages JSON body,
///   authenticated in full (the public evidence the CFG + injection legs run over).
///
/// The presentation is signed by `notary`.
pub fn build_anthropic_fixture(
    notary: &FixtureNotary,
    response_body: &str,
    connection_time: u64,
) -> EndpointPresentation {
    build_endpoint_fixture(
        notary,
        &EndpointSpec::anthropic_messages(),
        MESSAGES_PATH,
        response_body,
        connection_time,
    )
}

/// **Build an endpoint presentation fixture — the endpoint-agnostic producer.**
///
/// Constructs a realistic authenticated HTTP/1.1 transcript for ANY [`EndpointSpec`]:
///
/// - **Request (`sent`):** `{method} {path} HTTP/1.1`, `host: {server_name}`, and — when
///   the spec declares a secret header — that header with its value REDACTED (fill `X`,
///   NOT authenticated): the killer use case, prove the response WITHOUT revealing your
///   key. A public endpoint (`secret_header = None`) sends no secret at all.
/// - **Response (`recv`):** the status line + headers + the JSON body, authenticated in
///   full (the public evidence the CFG + injection legs run over).
///
/// The presentation is signed by `notary`. This models the tlsn notary + 2PC + a live
/// session against `server_name`; the genuine local run is [`crate::tlsn_live`].
pub fn build_endpoint_fixture(
    notary: &FixtureNotary,
    spec: &EndpointSpec,
    path: &str,
    response_body: &str,
    connection_time: u64,
) -> EndpointPresentation {
    // ── Request transcript. If a secret header is declared, its VALUE is redacted (fill
    // X); the header NAME stays. Everything else is authenticated.
    let secret_line = match &spec.secret_header {
        Some(sh) => format!("{}: {}\r\n", sh.name, sh.placeholder),
        None => String::new(),
    };
    let sent_str = format!(
        "{method} {path} HTTP/1.1\r\n\
         host: {host}\r\n\
         {secret_line}\
         accept: application/json\r\n\
         content-type: application/json\r\n\r\n",
        method = spec.method,
        host = spec.server_name,
    );
    let mut sent = sent_str.into_bytes();
    if let Some(sh) = &spec.secret_header {
        // Redact exactly the secret value bytes wherever the placeholder appears.
        if let Some(secret_start) = find_subslice(&sent, sh.placeholder.as_bytes()) {
            let secret_end = secret_start + sh.placeholder.len();
            for b in &mut sent[secret_start..secret_end] {
                *b = b'X';
            }
        }
    }

    // ── Response transcript — the JSON body authenticated in full.
    let recv = format!(
        "HTTP/1.1 200 OK\r\n\
         content-type: application/json\r\n\
         request-id: req_fixture\r\n\r\n\
         {response_body}"
    )
    .into_bytes();

    let pres = EndpointPresentation {
        verifying_key: notary.verifying_key(),
        server_name: spec.server_name.clone(),
        connection_time,
        sent,
        recv,
        notary_sig: [0u8; 64],
    };
    notary.sign(pres)
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || needle.len() > haystack.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

fn contains_subslice(haystack: &[u8], needle: &[u8]) -> bool {
    find_subslice(haystack, needle).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    const BODY: &str = r#"{"id":"msg_01","type":"message","role":"assistant","content":[{"type":"text","text":"hello"}],"stop_reason":"end_turn"}"#;

    #[test]
    fn honest_presentation_yields_body_and_hides_key() {
        let notary = FixtureNotary::from_seed(&[1u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let pres = build_anthropic_fixture(&notary, BODY, 1_700_000_000);

        let session =
            verify_anthropic_presentation(&pres, &cfg).expect("honest presentation verifies");
        assert_eq!(session.server_name, ANTHROPIC_SERVER_NAME);
        assert_eq!(session.response_body, BODY.as_bytes());
        // The api-key secret does not survive into the authenticated sent bytes.
        assert!(!contains_subslice(&pres.sent, b"MERCHANT-API-KEY"));
    }

    #[test]
    fn wrong_server_refused() {
        let notary = FixtureNotary::from_seed(&[2u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let mut pres = build_anthropic_fixture(&notary, BODY, 1);
        pres.server_name = "evil.example.com".to_string();
        let resigned = notary.sign(pres);
        assert!(matches!(
            verify_anthropic_presentation(&resigned, &cfg).unwrap_err(),
            AuthenticError::WrongServer { .. }
        ));
    }

    #[test]
    fn wrong_notary_refused() {
        let notary = FixtureNotary::from_seed(&[3u8; 32]);
        let other = FixtureNotary::from_seed(&[4u8; 32]);
        let cfg = AnthropicConfig::new(other.verifying_key());
        let pres = build_anthropic_fixture(&notary, BODY, 1);
        assert_eq!(
            verify_anthropic_presentation(&pres, &cfg).unwrap_err(),
            AuthenticError::WrongNotary
        );
    }

    #[test]
    fn tampered_disclosed_byte_breaks_signature() {
        let notary = FixtureNotary::from_seed(&[5u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let mut pres = build_anthropic_fixture(&notary, BODY, 1);
        // Flip a byte in the authenticated response body.
        let n = pres.recv.len();
        pres.recv[n - 5] ^= 0xFF;
        assert_eq!(
            verify_anthropic_presentation(&pres, &cfg).unwrap_err(),
            AuthenticError::BadNotarySignature
        );
    }

    #[test]
    fn disclosed_api_key_is_refused() {
        // A presentation that FAILED to redact the key (the secret in the sent bytes) is
        // refused even if correctly signed — the killer property is enforced.
        let notary = FixtureNotary::from_seed(&[6u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let mut pres = build_anthropic_fixture(&notary, BODY, 1);
        // Splice the secret back into the sent bytes and re-sign.
        let leaked =
            format!("POST /v1/messages HTTP/1.1\r\nx-api-key: {API_KEY_PLACEHOLDER}\r\n\r\n");
        pres.sent = leaked.into_bytes();
        let resigned = notary.sign(pres);
        assert_eq!(
            verify_anthropic_presentation(&resigned, &cfg).unwrap_err(),
            AuthenticError::ApiKeyDisclosed
        );
    }
}
