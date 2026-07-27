//! **The zkOracle capstone** — the 3-leg attestation + verifier, mirroring
//! `metatheory/Dregg2/Crypto/ZkOracle.lean::zkOracle_sound`.
//!
//! ```lean
//! theorem zkOracle_sound … :
//!     (∃ w, Deco.DecoRelation … decoStmt w) ∧          -- authentic
//!     body ∈ jsonGrammar.language ∧                     -- well-formed
//!     InjectionFree field                               -- injection-free
//! ```
//!
//! A [`ZkOracleAttestation`] carries all three legs' evidence; [`verify_zkoracle`]
//! is the Rust realization of the composition: it ACCEPTS iff all three verify, and
//! refuses (with the failing leg named) otherwise.
//!
//! ## The cross-leg weld — ONE committed response, not three independent objects
//!
//! Verifying the three legs is not enough: they must be about the SAME request. A
//! [`content_commitment`] — a Poseidon2 sponge over the **authenticated response body**
//! (the SAME `hash_bytes` primitive the content-root uses) — is threaded across all three:
//!
//! - **authentic** yields the response body; the verifier recomputes its commitment and
//!   refuses any attestation whose committed value disagrees ([`ZkOracleError::CrossLegMismatch`]);
//! - **well-formed** checks its certificate against that same authenticated body;
//! - **injection-free** runs over a committed SUBSTRING of that same authenticated body
//!   ([`FieldSpan`]) — the user field is extracted from the authenticated bytes, NOT a
//!   free-standing input a splicer could swap.
//!
//! So a spliced attestation (a well-formed cert / an injection-free field about body A
//! stapled onto an authentic session for body B) is REFUSED — the legs are bound to ONE
//! response. This is the 3-way analogue of the DECO body-binding in `bridge::stripe_deco`.

use crate::authentic::{
    AuthenticError, AuthenticSession, EndpointConfig, EndpointPresentation,
    verify_endpoint_presentation,
};
use crate::cfg::{CfgError, CompactCert, prove_cfg_compact, verify_cfg_compact};
use crate::injection::injection_free;
use crate::zk_leg::{ZkInjectionProof, ZkLegError, prove_injection_leg, verify_injection_leg};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_bytes;

/// **The ONE shared content commitment** binding the three legs to a single response — a
/// Poseidon2 sponge over the authenticated response body, the SAME `hash_bytes` primitive
/// the content-root uses (4-byte-packed limbs → the Poseidon2 sponge). [`verify_zkoracle`]
/// recomputes this over the AUTHENTICATED body and refuses any attestation whose committed
/// value, certificate, or injection field is not about THAT body.
pub fn content_commitment(response_body: &[u8]) -> BabyBear {
    hash_bytes(response_body)
}

/// A committed byte range within the authenticated response body — the location the
/// injection-checked field is extracted FROM (so the field is a committed substring of the
/// authenticated bytes, not a free-standing input).
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct FieldSpan {
    /// The start offset of the field within the authenticated response body.
    pub offset: usize,
    /// The field length in bytes.
    pub len: usize,
}

impl FieldSpan {
    /// Extract the field bytes from `body`, or `None` if the span lies out of range.
    pub fn extract<'a>(&self, body: &'a [u8]) -> Option<&'a [u8]> {
        let end = self.offset.checked_add(self.len)?;
        body.get(self.offset..end)
    }
}

/// A full zkOracle attestation — the three legs' evidence bundled, all bound to ONE
/// authenticated response by the shared [`content_commitment`].
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ZkOracleAttestation {
    /// **Authentic leg** — the verified tlsn/MPC-TLS presentation of the Anthropic
    /// `POST /v1/messages` session (x-api-key redacted).
    pub presentation: EndpointPresentation,
    /// **Well-formed leg** — the compact JSON CFG parse certificate over the
    /// authenticated response body: the leftmost rule sequence (O(tokens); replayed
    /// against the re-tokenized body, `CfgCompact.lean::Replay`-shaped; `expand_compact`
    /// rebuilds the `producesChain` form).
    pub cfg_cert: CompactCert,
    /// **Injection-free leg** — the committed span (within the authenticated response body)
    /// the guard extracts the field from and checks against the `neg injectionTemplate`
    /// matcher (contains no `{{`). The field is a substring of the authenticated bytes.
    pub field_span: FieldSpan,
    /// **The cross-leg weld** — the shared [`content_commitment`] over the authenticated
    /// response body. The verifier recomputes it and refuses a mismatch, binding all three
    /// legs to the SAME response.
    pub content_commit: BabyBear,
    /// **The STARK-carried injection leg** (optional) — a real `stark::prove` of the
    /// pinned injection DFA's run over the field ([`crate::zk_leg`]). When present the
    /// verifier checks it FAIL-CLOSED (a wrong-run/forged/injecting proof refuses the
    /// whole attestation); when absent leg 3 is the cleartext matcher as before.
    pub zk_injection: Option<ZkInjectionProof>,
    /// **The REAL tlsn presentation** (optional) — the bincode-serialized genuine `tlsn`
    /// `Presentation` from a live MPC-TLS 2PC roundtrip. When present, [`verify_zkoracle_live`]
    /// (feature `tlsn-live`) authenticates leg 1 by the REAL `presentation.verify()` — a
    /// trustless 2PC notary — instead of the modeled ed25519 [`Self::presentation`] carrier.
    /// The default [`verify_zkoracle`] path ignores this and uses the modeled carrier, so a
    /// light default attestation sets it `None`. Always present (not feature-gated) so the
    /// struct shape is uniform; only the live *verifier* links the heavy `tlsn` backend.
    pub tlsn_presentation: Option<Vec<u8>>,
}

/// The verified output: the authenticated session (server + response body) once all three
/// legs pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedZkOracle {
    /// The authenticated Anthropic session (server, time, response body).
    pub session: AuthenticSession,
    /// **WHAT ACTUALLY VOUCHED for the body** — the provenance the authentic leg was
    /// verified under. A [`VerifiedZkOracle`] carrying [`AuthenticProvenance::SelfSignedFixture`]
    /// says NOTHING about where the bytes came from; only [`AuthenticProvenance::MpcTls`]
    /// carries transport provenance. Read it before believing an accept.
    pub provenance: AuthenticProvenance,
}

// ─────────────────────────────────────────────────────────────────────────────
// THE PROVENANCE GATE — what actually vouches for "these bytes came from the endpoint".
//
// The three legs (authentic ∧ well-formed ∧ injection-free) are welded to ONE response by
// the shared `content_commitment`, but that weld says nothing about the SOURCE of the
// response: it binds the legs to each other, not to a real endpoint. The source is leg 1's
// job — and leg 1 has two utterly different realizations that the type system did not
// previously distinguish:
//
//   * `EndpointPresentation` + `FixtureNotary` — a SELF-SIGNED TEST DOUBLE. The prover
//     CONSTRUCTS the transcript and signs it with a key it holds itself. It can mint any
//     body it likes, sign it, and every leg goes green. This proves the PRODUCE→VERIFY
//     plumbing hermetically and NOTHING about provenance.
//   * `tlsn_presentation` — a REAL MPC-TLS presentation. A separate notary co-derived the
//     session keys, saw no plaintext, and signed an attestation over a transcript the
//     prover could not forge; `presentation.verify()` is genuine crypto against a real
//     cert chain.
//
// Before this gate both realizations flowed into the SAME `verify_zkoracle`, which always
// read the fixture — so every narrator's "provably came from the model" was, on every path
// it actually used, a self-signed fixture. `AuthenticPolicy::RequireMpcTls` is the tooth:
// on a live path a fixture-only attestation is REFUSED, fail-closed, before any leg runs.
// ─────────────────────────────────────────────────────────────────────────────

/// **WHAT VOUCHES for an attestation's authentic leg** — the provenance of "these bytes
/// came from the endpoint". Read it off an attestation with [`authentic_provenance`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AuthenticProvenance {
    /// ⚑ **A SELF-SIGNED TEST DOUBLE — NO PROVENANCE WHATSOEVER.** The attestation carries
    /// only the modeled ed25519 [`crate::authentic::FixtureNotary`] carrier: the prover
    /// built the transcript and signed it with a key it holds itself, so it can mint any
    /// body it likes and every leg still verifies. Exercises the PRODUCE→VERIFY plumbing
    /// hermetically; asserts nothing about where the bytes came from. REFUSED by
    /// [`AuthenticPolicy::RequireMpcTls`].
    SelfSignedFixture,
    /// The attestation carries a REAL MPC-TLS presentation ([`ZkOracleAttestation::tlsn_presentation`]):
    /// a separate notary co-derived the session keys, saw no plaintext, and signed a
    /// transcript the prover could not forge. Whether that presentation actually VERIFIES
    /// (and against which cert chain / notary pin) is the live verifier's job — this is the
    /// structural claim the attestation makes, which the crypto then adjudicates.
    MpcTls,
}

/// **Read the provenance an attestation CLAIMS** for its authentic leg — a structural
/// check (does it carry a real MPC-TLS presentation at all?), available in the light
/// default build with no tlsn backend. It is the cheap gate that makes a fixture-only
/// attestation refusable on a live path *before* any crypto runs; the real
/// `presentation.verify()` then adjudicates whether the claim holds.
pub fn authentic_provenance(att: &ZkOracleAttestation) -> AuthenticProvenance {
    match att.tlsn_presentation {
        Some(_) => AuthenticProvenance::MpcTls,
        None => AuthenticProvenance::SelfSignedFixture,
    }
}

/// **The provenance a verifier DEMANDS of the authentic leg** — the policy that separates a
/// hermetic plumbing test from a live attestation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AuthenticPolicy {
    /// ⚑ **TEST DOUBLE ADMITTED.** Leg 1 is verified as the self-signed ed25519 fixture
    /// carrier ([`ZkOracleAttestation::presentation`]) — *always*, even if the attestation
    /// also happens to carry a real MPC-TLS presentation. Use ONLY for hermetic tests of
    /// the PRODUCE→VERIFY plumbing. An accept under this policy is NOT evidence the body
    /// came from any endpoint: the prover signed its own transcript, so it could have
    /// minted any body it liked. This is the legacy [`verify_zkoracle`] behaviour,
    /// preserved verbatim.
    AllowFixture,
    /// **LIVE.** Leg 1 MUST be a real MPC-TLS presentation. A fixture-only attestation is
    /// REFUSED ([`ZkOracleError::FixtureOnLivePath`]) before any leg runs, and the real
    /// presentation must then pass genuine `presentation.verify()` — so an accept under
    /// this policy DOES carry transport provenance.
    RequireMpcTls,
}

impl AuthenticPolicy {
    /// Whether this policy admits `provenance` as leg 1.
    pub fn admits(&self, provenance: AuthenticProvenance) -> bool {
        match self {
            AuthenticPolicy::AllowFixture => true,
            AuthenticPolicy::RequireMpcTls => provenance == AuthenticProvenance::MpcTls,
        }
    }
}

/// Which leg refused the attestation (any ONE failing → the whole attestation is refused).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZkOracleError {
    /// The authentic leg failed (bad presentation: forged/tampered/wrong-server/leaked-key).
    NotAuthentic(AuthenticError),
    /// The well-formed leg failed (the CFG certificate does not certify the body).
    NotWellFormed(CfgError),
    /// The injection-free leg failed (the user field carries the `{{` handlebars delimiter).
    Injection,
    /// **The cross-leg weld refused** — a leg's object is not about the authenticated
    /// response: the shared content commitment disagrees with the authentic body, or the
    /// injection field span lies outside it. A spliced attestation (evidence about a
    /// DIFFERENT body than the authentic session) fails here.
    CrossLegMismatch,
    /// The STARK-carried injection leg refused (wrong run / forged proof). An
    /// `Injecting` verdict from the leg surfaces as [`ZkOracleError::Injection`].
    BadZkLeg(ZkLegError),
    /// **The LIVE authentic leg refused** — the real `tlsn` `presentation.verify()` failed
    /// (a tampered/forged presentation, a wrong server pin, or a missing presentation), as
    /// surfaced by the [`MpcTlsLeg`] the caller supplied. Carries the verifier's message.
    NotAuthenticLive(String),
    /// **THE PROVENANCE GATE REFUSED — a self-signed fixture was offered on a LIVE path.**
    /// The attestation's authentic leg is only the modeled ed25519 [`crate::authentic::FixtureNotary`]
    /// carrier (the prover signed its own transcript), but the verifier demanded
    /// [`AuthenticPolicy::RequireMpcTls`]. Nothing vouches for where these bytes came from,
    /// so the attestation is refused before any leg runs. This is the tooth that stops a
    /// test double being consumed as a live proof of model provenance.
    FixtureOnLivePath,
    /// **The caller supplied no MPC-TLS backend** — leg 1 was to be a real
    /// `presentation.verify()`, but the [`MpcTlsLeg`] handed in was [`NoMpcTlsBackend`], which
    /// authenticates nothing. Fail-CLOSED: an uncheckable live leg is refused, never waved
    /// through onto the fixture carrier sitting right next to it.
    ///
    /// ⚑ This used to mean "this crate was compiled without the `tlsn-live` feature", which
    /// made a SECURITY-LOAD-BEARING branch depend on which OTHER workspace members cargo had
    /// been asked about. It is now a value the caller passes, visible at the call site. The
    /// real backend is `dregg_zkoracle_live::TlsnLeg`.
    LiveBackendUnavailable,
}

impl core::fmt::Display for ZkOracleError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ZkOracleError::NotAuthentic(e) => write!(f, "authentic leg refused: {e}"),
            ZkOracleError::NotWellFormed(e) => write!(f, "well-formed leg refused: {e:?}"),
            ZkOracleError::Injection => {
                write!(
                    f,
                    "injection-free leg refused: the user field contains the {{{{ delimiter"
                )
            }
            ZkOracleError::CrossLegMismatch => {
                write!(
                    f,
                    "cross-leg weld refused: a leg's evidence is not about the authenticated response"
                )
            }
            ZkOracleError::BadZkLeg(e) => {
                write!(f, "STARK injection leg refused: {e:?}")
            }
            ZkOracleError::NotAuthenticLive(msg) => {
                write!(
                    f,
                    "live authentic leg refused (real tlsn presentation): {msg}"
                )
            }
            ZkOracleError::FixtureOnLivePath => {
                write!(
                    f,
                    "provenance gate refused: the authentic leg is a SELF-SIGNED FIXTURE \
                     (the prover signed its own transcript) but this path requires a real \
                     MPC-TLS presentation — nothing vouches for where these bytes came from"
                )
            }
            ZkOracleError::LiveBackendUnavailable => {
                write!(
                    f,
                    "live authentic leg cannot be checked: the caller supplied \
                     NoMpcTlsBackend, so presentation.verify() was never run (refusing \
                     fail-closed). Pass a real MpcTlsLeg (dregg_zkoracle_live::TlsnLeg)."
                )
            }
        }
    }
}

impl std::error::Error for ZkOracleError {}

/// **VERIFY a zkOracle attestation** — the 3-leg composition (`zkOracle_sound`).
///
/// ACCEPTS iff:
///   1. **authentic** — the tlsn presentation verifies (server pinned, notary pinned,
///      signature valid, api-key redacted), yielding the authenticated response body;
///   2. **well-formed** — the CFG parse certificate certifies THAT authenticated body lies
///      in the JSON context-free language;
///   3. **injection-free** — the user field matches `neg injectionTemplate` (no `{{`).
///
/// Any leg failing → the attestation is REFUSED (the failing leg named). The catch
/// genuinely discriminates: a benign field passes leg 3, a `{{`-bearing field fails it.
/// ⚑ **PROVENANCE:** this entry admits a SELF-SIGNED FIXTURE as leg 1
/// ([`AuthenticPolicy::AllowFixture`]) — an accept proves the three legs compose over ONE
/// response, NOT that the response came from any endpoint. For a live attestation use
/// [`verify_zkoracle_with_policy`] with [`AuthenticPolicy::RequireMpcTls`].
pub fn verify_zkoracle(
    att: &ZkOracleAttestation,
    config: &EndpointConfig,
) -> Result<VerifiedZkOracle, ZkOracleError> {
    verify_zkoracle_with_policy(att, config, AuthenticPolicy::AllowFixture, &NoMpcTlsBackend)
}

/// **The MPC-TLS authenticator for leg 1** — the seam where a REAL `tlsn`
/// `presentation.verify()` plugs in.
///
/// This crate never links `tlsn`. It defines the obligation and the fail-closed default;
/// `dregg_zkoracle_live::TlsnLeg` is the implementation that runs genuine 2PC crypto against
/// the pinned server and (optionally) a pinned notary key.
///
/// ⚑ WHY THIS IS A TRAIT AND NOT A `#[cfg(feature = "tlsn-live")]`. It used to be a
/// `#[cfg]`/`#[cfg(not)]` PAIR over this exact function: with the feature on, real crypto;
/// with it off, an immediate refusal. Cargo UNIFIES features across a workspace resolve, so
/// which of those two bodies a build got was decided by which OTHER packages happened to be
/// selected — `cargo test -p dregg-zkoracle-prove` compiled one and `cargo test --workspace`
/// the other, because an unrelated member (`dregg-oracle`) had the feature in its `default`.
/// A security-load-bearing branch must not be a function of the package selection. Now the
/// caller names the backend it has, and the choice is visible at the call site.
pub trait MpcTlsLeg {
    /// Authenticate `presentation_bytes` as a genuine MPC-TLS session with `expected_server`,
    /// yielding the authenticated session (the response body legs 2–4 then run over).
    fn authenticate(
        &self,
        presentation_bytes: &[u8],
        expected_server: &str,
    ) -> Result<AuthenticSession, ZkOracleError>;
}

/// **The fail-closed backend: authenticates NOTHING.** A verifier holding this cannot check a
/// live leg, so it refuses one ([`ZkOracleError::LiveBackendUnavailable`]) rather than falling
/// back onto the self-signed fixture carrier the attestation also has — that fallback would be
/// precisely the laundering the provenance gate exists to stop.
///
/// It is a NAMED VALUE, not an absence: a call site passing it says so in the source, where
/// the old `#[cfg(not(feature = "tlsn-live"))]` said nothing at all.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NoMpcTlsBackend;

impl MpcTlsLeg for NoMpcTlsBackend {
    fn authenticate(&self, _: &[u8], _: &str) -> Result<AuthenticSession, ZkOracleError> {
        Err(ZkOracleError::LiveBackendUnavailable)
    }
}

/// **VERIFY a zkOracle attestation UNDER AN EXPLICIT PROVENANCE POLICY** — the entry that
/// decides *what is allowed to vouch* for the authentic leg.
///
/// - [`AuthenticPolicy::AllowFixture`] — leg 1 is the modeled ed25519 carrier (the legacy
///   [`verify_zkoracle`] behaviour, unchanged). Hermetic plumbing only.
/// - [`AuthenticPolicy::RequireMpcTls`] — **the live path.** A fixture-only attestation is
///   REFUSED ([`ZkOracleError::FixtureOnLivePath`]) before any leg runs. A real MPC-TLS
///   presentation is authenticated by `mpctls`, the [`MpcTlsLeg`] the CALLER supplies, against
///   the pinned `config.expected_server()`. A caller holding [`NoMpcTlsBackend`] cannot check
///   the leg at all and is refused fail-closed ([`ZkOracleError::LiveBackendUnavailable`]) —
///   never silently downgraded onto the fixture.
///
/// The authenticated body (whichever leg produced it) then drives the SAME cross-leg weld +
/// well-formed + injection-free + STARK legs, so the splice refusal is identical on both
/// paths.
pub fn verify_zkoracle_with_policy(
    att: &ZkOracleAttestation,
    config: &EndpointConfig,
    policy: AuthenticPolicy,
    mpctls: &dyn MpcTlsLeg,
) -> Result<VerifiedZkOracle, ZkOracleError> {
    // ── THE PROVENANCE GATE ── refuse a test double on a live path BEFORE any leg runs.
    if !policy.admits(authentic_provenance(att)) {
        return Err(ZkOracleError::FixtureOnLivePath);
    }
    // THE POLICY selects which leg authenticates — never the attestation's own contents.
    // Dispatching on the payload would mean a verifier's guarantee silently changed with
    // the data it was handed (an attestation that happens to carry a real presentation
    // would get checked differently from one that does not), which is exactly the kind of
    // implicit switch that let "authentic" mean two different things in the first place.
    // The policy is the verifier's DECISION about what it is willing to trust; it must
    // pick the leg deterministically, and the reported provenance is whatever was in fact
    // verified.
    match policy {
        // Leg 1 — the modeled ed25519 carrier → the authenticated response body. Verbatim
        // legacy behaviour, including on an attestation that also carries a live leg.
        AuthenticPolicy::AllowFixture => {
            let session = verify_endpoint_presentation(&att.presentation, config)
                .map_err(ZkOracleError::NotAuthentic)?;
            verify_legs_over_session(att, session, AuthenticProvenance::SelfSignedFixture)
        }
        // Leg 1 — the REAL MPC-TLS presentation, adjudicated by genuine tlsn crypto in
        // whatever backend the caller handed in.
        AuthenticPolicy::RequireMpcTls => {
            let bytes = att
                .tlsn_presentation
                .as_ref()
                .ok_or(ZkOracleError::FixtureOnLivePath)?;
            let session = mpctls.authenticate(bytes, config.expected_server())?;
            verify_legs_over_session(att, session, AuthenticProvenance::MpcTls)
        }
    }
}

/// **BUILD an attestation over an already-AUTHENTICATED response body.**
///
/// Every live endpoint prover (coinbase spot, github commit, generic URL) does the same three
/// things once its MPC-TLS session has produced an authenticated body: prove the CFG
/// certificate over THAT body, commit to it, and package the result with the real presentation
/// bytes. That is this function, and it links no `tlsn` — the caller has already reduced its
/// session to `(server_name, connection_time, sent_redacted, body)`.
///
/// The modeled `presentation` it builds carries a ZERO `notary_sig`: it is an UNSIGNED
/// envelope holding the authenticated request line (so the endpoint's fact-extractors can
/// recover the request target), NOT a second authentication. The real authentication is
/// `tlsn_presentation`, and a verifier of a live attestation MUST use
/// [`AuthenticPolicy::RequireMpcTls`] — the modeled carrier would not verify and is never
/// consulted on that path.
#[allow(clippy::too_many_arguments)]
pub fn attestation_over_authenticated_body(
    notary_alg: &str,
    notary_data: &[u8],
    server_name: &str,
    connection_time: u64,
    sent_redacted: &[u8],
    body: &[u8],
    tlsn_presentation: Vec<u8>,
) -> Result<ZkOracleAttestation, ZkOracleError> {
    use crate::authentic::TlsnVerifyingKey;

    // Leg 2 — well-formed JSON CFG certificate over the AUTHENTICATED body.
    let cfg_cert = prove_cfg_compact(body).map_err(ZkOracleError::NotWellFormed)?;
    // The cross-leg weld. The injection leg is vacuous for these read-only endpoints: there
    // is no user-supplied field, so the empty span is injection-free by inspection.
    let content_commit = content_commitment(body);
    let mut recv = b"HTTP/1.1 200 OK\r\ncontent-type: application/json\r\n\r\n".to_vec();
    recv.extend_from_slice(body);
    Ok(ZkOracleAttestation {
        presentation: EndpointPresentation {
            verifying_key: TlsnVerifyingKey {
                alg: notary_alg.to_string(),
                data: notary_data.to_vec(),
            },
            server_name: server_name.to_string(),
            connection_time,
            sent: sent_redacted.to_vec(),
            recv,
            notary_sig: [0u8; 64],
        },
        cfg_cert,
        field_span: FieldSpan { offset: 0, len: 0 },
        content_commit,
        zk_injection: None,
        tlsn_presentation: Some(tlsn_presentation),
    })
}

/// The shared legs 2–4 over an already-authenticated session: the cross-leg weld, the
/// well-formed (CFG) leg, the injection-free leg, and the optional STARK injection leg.
/// Both leg-1 routes — the modeled fixture carrier and a real [`MpcTlsLeg`] — bind their
/// downstream evidence to the SAME authenticated body through this. `pub` because
/// `dregg-zkoracle-live` reaches it after authenticating a session with genuine tlsn crypto.
pub fn verify_legs_over_session(
    att: &ZkOracleAttestation,
    session: AuthenticSession,
    provenance: AuthenticProvenance,
) -> Result<VerifiedZkOracle, ZkOracleError> {
    // ── THE CROSS-LEG WELD ──
    // Recompute the shared content commitment over the AUTHENTICATED body and require the
    // attestation's committed value to equal it. This binds every downstream leg's object
    // to ONE response: a spliced attestation (a commitment / certificate / field about a
    // DIFFERENT body than the authentic session) is refused HERE.
    if att.content_commit != content_commitment(&session.response_body) {
        return Err(ZkOracleError::CrossLegMismatch);
    }

    // Leg 2 — well-formed, over the committed authenticated body (binds well-formedness to
    // the genuine session, not an arbitrary blob).
    verify_cfg_compact(&att.cfg_cert, &session.response_body)
        .map_err(ZkOracleError::NotWellFormed)?;

    // Leg 3 — injection-free, over a COMMITTED SUBSTRING of the authenticated body. The
    // user field is EXTRACTED from the authenticated bytes (a span the verifier reads
    // itself), not a free-standing input a splicer could swap for a benign string while
    // the real authenticated content injects.
    let field = att
        .field_span
        .extract(&session.response_body)
        .ok_or(ZkOracleError::CrossLegMismatch)?;
    if !injection_free(field) {
        return Err(ZkOracleError::Injection);
    }

    // The STARK-carried injection leg, when present: the proof must be the field's
    // genuine run of the pinned DFA (fail-closed — a stapled-on bad proof refuses the
    // attestation even though the cleartext matcher already passed).
    if let Some(leg) = &att.zk_injection {
        verify_injection_leg(field, leg).map_err(|e| match e {
            ZkLegError::Injecting => ZkOracleError::Injection,
            other => ZkOracleError::BadZkLeg(other),
        })?;
    }

    Ok(VerifiedZkOracle {
        session,
        provenance,
    })
}

/// **PRODUCE a zkOracle attestation** from a verified presentation + a user field.
///
/// Re-verifies the presentation (to extract the authenticated body), proves the CFG
/// certificate over that exact body, and bundles the user field. The result is an
/// attestation [`verify_zkoracle`] accepts — UNLESS the user field is an injection
/// attempt, in which case the prover REFUSES to produce it ([`ProveError::Injection`]):
/// the guard cannot mint an attestation for an injecting request (mirroring the Lean
/// `malicious_not_injection_free`).
pub fn prove_zkoracle(
    presentation: EndpointPresentation,
    user_field: Vec<u8>,
    config: &EndpointConfig,
) -> Result<ZkOracleAttestation, ProveError> {
    let session =
        verify_endpoint_presentation(&presentation, config).map_err(ProveError::NotAuthentic)?;
    // The guard refuses to attest an injecting field up front.
    if !injection_free(&user_field) {
        return Err(ProveError::Injection);
    }
    // The field MUST be a committed substring of the AUTHENTICATED response body — a
    // free-standing field unrelated to the session cannot be attested (the cross-leg weld:
    // the injection-checked object is part of the same authenticated response the other
    // legs are about).
    let offset =
        find_subslice(&session.response_body, &user_field).ok_or(ProveError::FieldNotInResponse)?;
    let field_span = FieldSpan {
        offset,
        len: user_field.len(),
    };
    let cfg_cert = prove_cfg_compact(&session.response_body).map_err(ProveError::NotWellFormed)?;
    let content_commit = content_commitment(&session.response_body);
    Ok(ZkOracleAttestation {
        presentation,
        cfg_cert,
        field_span,
        content_commit,
        zk_injection: None,
        tlsn_presentation: None,
    })
}

/// [`prove_zkoracle`] + a REAL STARK on the injection leg: the attestation additionally
/// carries a `stark::prove` of the pinned injection DFA's run over the field
/// ([`crate::zk_leg`]), which [`verify_zkoracle`] checks fail-closed.
pub fn prove_zkoracle_with_stark(
    presentation: EndpointPresentation,
    user_field: Vec<u8>,
    config: &EndpointConfig,
) -> Result<ZkOracleAttestation, ProveError> {
    let mut att = prove_zkoracle(presentation, user_field.clone(), config)?;
    att.zk_injection = Some(prove_injection_leg(&user_field).ok_or(ProveError::Injection)?);
    Ok(att)
}

/// Locate `needle` as a substring of `haystack`; an empty needle is at offset 0.
fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() {
        return Some(0);
    }
    if needle.len() > haystack.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

/// Why the prover could not PRODUCE an attestation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProveError {
    /// The presentation does not verify (cannot build an attestation over a bad session).
    NotAuthentic(AuthenticError),
    /// The authenticated body is not well-formed JSON (no certificate exists).
    NotWellFormed(CfgError),
    /// The user field is an injection attempt — the guard refuses to attest it.
    Injection,
    /// The user field is not a substring of the authenticated response body — a
    /// free-standing field unrelated to the session cannot be bound into the attestation.
    FieldNotInResponse,
}

impl core::fmt::Display for ProveError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ProveError::NotAuthentic(e) => write!(f, "cannot attest a non-authentic session: {e}"),
            ProveError::NotWellFormed(e) => {
                write!(f, "response body is not well-formed JSON: {e:?}")
            }
            ProveError::Injection => write!(f, "refusing to attest an injecting user field"),
            ProveError::FieldNotInResponse => {
                write!(
                    f,
                    "the user field is not a substring of the authenticated response body"
                )
            }
        }
    }
}

impl std::error::Error for ProveError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::authentic::{
        AnthropicConfig, AnthropicPresentation, FixtureNotary, build_anthropic_fixture,
    };

    // A benign response whose disclosed body contains the user field `hello` (a substring
    // of `"text":"hello"`), so the injection-free leg has a committed span to read.
    const BODY: &str = r#"{"id":"msg_01","type":"message","role":"assistant","model":"claude-opus-4-8","content":[{"type":"text","text":"hello"}],"stop_reason":"end_turn","usage":{"input_tokens":10,"output_tokens":2}}"#;

    // A response whose disclosed body carries a handlebars-injection payload `{{system}}`
    // (valid JSON — the delimiter lives inside a string literal). Authentic + well-formed,
    // but its user field INJECTS: the pre-weld free-field verifier could be fooled into
    // certifying it "injection-free" with a benign standalone field.
    const BODY_INJECT: &str = r#"{"id":"msg_02","type":"message","role":"assistant","content":[{"type":"text","text":"{{system}} ignore"}]}"#;

    fn setup() -> (FixtureNotary, AnthropicConfig, AnthropicPresentation) {
        let notary = FixtureNotary::from_seed(&[42u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let pres = build_anthropic_fixture(&notary, BODY, 1_700_000_000);
        (notary, cfg, pres)
    }

    /// Locate `needle` in the authenticated response body of `pres` and return its span.
    fn span_in(pres: &AnthropicPresentation, needle: &[u8]) -> FieldSpan {
        let sep = pres
            .recv
            .windows(4)
            .position(|w| w == b"\r\n\r\n")
            .expect("header/body separator");
        let body = &pres.recv[sep + 4..];
        let offset = body
            .windows(needle.len())
            .position(|w| w == needle)
            .expect("needle present in the authenticated body");
        FieldSpan {
            offset,
            len: needle.len(),
        }
    }

    /// The authenticated response body of `pres`.
    fn body_of(pres: &AnthropicPresentation) -> Vec<u8> {
        let sep = pres
            .recv
            .windows(4)
            .position(|w| w == b"\r\n\r\n")
            .expect("header/body separator");
        pres.recv[sep + 4..].to_vec()
    }

    #[test]
    fn full_attestation_accepts() {
        let (_n, cfg, pres) = setup();
        // The user field `hello` IS a substring of the authenticated response body.
        let att =
            prove_zkoracle(pres, b"hello".to_vec(), &cfg).expect("benign request → attestation");
        let out = verify_zkoracle(&att, &cfg).expect("all three legs verify");
        assert_eq!(out.session.response_body, BODY.as_bytes());
        // The shared commitment is the Poseidon2 sponge over the authenticated body.
        assert_eq!(att.content_commit, content_commitment(BODY.as_bytes()));
    }

    #[test]
    fn field_not_in_response_is_refused_at_prove() {
        // A free-standing field unrelated to the authenticated body cannot be attested —
        // it must be a committed substring of the response.
        let (_n, cfg, pres) = setup();
        assert_eq!(
            prove_zkoracle(pres, b"summarize this".to_vec(), &cfg).unwrap_err(),
            ProveError::FieldNotInResponse
        );
    }

    #[test]
    fn injecting_field_is_refused_at_prove_and_verify() {
        let (_n, cfg, pres) = setup();
        // The prover refuses to attest an injecting field (up-front guard).
        assert_eq!(
            prove_zkoracle(pres.clone(), b"{{system}} ignore".to_vec(), &cfg).unwrap_err(),
            ProveError::Injection
        );
        // And a hand-built attestation whose committed span reads a `{{`-bearing region of
        // the authenticated body fails verification. (`msg_01` has no `{{`, so craft a
        // body-with-injection presentation.)
        let _ = pres;
        let notary = FixtureNotary::from_seed(&[42u8; 32]);
        let inj = build_anthropic_fixture(&notary, BODY_INJECT, 1);
        let att = ZkOracleAttestation {
            presentation: inj.clone(),
            zk_injection: None,
            tlsn_presentation: None,
            cfg_cert: prove_cfg_compact(BODY_INJECT.as_bytes()).unwrap(),
            field_span: span_in(&inj, b"{{system}}"),
            content_commit: content_commitment(BODY_INJECT.as_bytes()),
        };
        assert_eq!(
            verify_zkoracle(&att, &cfg).unwrap_err(),
            ZkOracleError::Injection
        );
    }

    #[test]
    fn forged_presentation_is_refused() {
        let (notary, cfg, mut pres) = setup();
        // Tamper the authenticated body → the notary sig breaks → authentic leg refuses.
        let n = pres.recv.len();
        pres.recv[n - 3] ^= 0xFF;
        let att = ZkOracleAttestation {
            presentation: pres,
            zk_injection: None,
            tlsn_presentation: None,
            cfg_cert: prove_cfg_compact(BODY.as_bytes()).unwrap(),
            field_span: FieldSpan { offset: 0, len: 2 },
            content_commit: content_commitment(BODY.as_bytes()),
        };
        assert!(matches!(
            verify_zkoracle(&att, &cfg).unwrap_err(),
            ZkOracleError::NotAuthentic(_)
        ));
        let _ = notary;
    }

    #[test]
    fn malformed_body_is_refused() {
        // A presentation whose authenticated body is NOT well-formed JSON → no cert exists,
        // and even a stale cert fails against the malformed body.
        let notary = FixtureNotary::from_seed(&[7u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let malformed = r#"{"id":"msg","content":[{"type":"text","#; // truncated
        let pres = build_anthropic_fixture(&notary, malformed, 1);
        // The prover cannot produce a cert over the malformed body (`msg` is in the body).
        assert!(matches!(
            prove_zkoracle(pres.clone(), b"msg".to_vec(), &cfg),
            Err(ProveError::NotWellFormed(_))
        ));
        // A cert borrowed from a well-formed body does not certify the malformed one; the
        // commitment is over the (malformed) authenticated body so the weld passes to leg 2.
        let att = ZkOracleAttestation {
            presentation: pres.clone(),
            zk_injection: None,
            tlsn_presentation: None,
            cfg_cert: prove_cfg_compact(BODY.as_bytes()).unwrap(),
            field_span: span_in(&pres, b"msg"),
            content_commit: content_commitment(malformed.as_bytes()),
        };
        assert!(matches!(
            verify_zkoracle(&att, &cfg).unwrap_err(),
            ZkOracleError::NotWellFormed(_)
        ));
    }

    #[test]
    fn each_leg_fails_independently() {
        // A single hostile mutation per leg, holding the other two honest — proves each
        // leg is load-bearing (the catch genuinely discriminates).
        let (notary, cfg, pres) = setup();

        // (a) authentic broken, well-formed + injection-free honest.
        let mut bad_auth = pres.clone();
        bad_auth.server_name = "evil.com".to_string();
        let bad_auth = notary.sign(bad_auth);
        let att_a = ZkOracleAttestation {
            presentation: bad_auth,
            zk_injection: None,
            tlsn_presentation: None,
            cfg_cert: prove_cfg_compact(BODY.as_bytes()).unwrap(),
            field_span: span_in(&pres, b"hello"),
            content_commit: content_commitment(BODY.as_bytes()),
        };
        assert!(matches!(
            verify_zkoracle(&att_a, &cfg),
            Err(ZkOracleError::NotAuthentic(_))
        ));

        // (b) well-formed broken (cert for a different body), authentic + injection honest.
        // The commitment is over the real authenticated body, so the weld passes to leg 2.
        let att_b = ZkOracleAttestation {
            presentation: pres.clone(),
            zk_injection: None,
            tlsn_presentation: None,
            cfg_cert: prove_cfg_compact(br#"{"other":true}"#).unwrap(),
            field_span: span_in(&pres, b"hello"),
            content_commit: content_commitment(BODY.as_bytes()),
        };
        assert!(matches!(
            verify_zkoracle(&att_b, &cfg),
            Err(ZkOracleError::NotWellFormed(_))
        ));

        // (c) injection broken (the committed span reads a `{{` region of the authentic
        // body), authentic + well-formed honest.
        let inj = build_anthropic_fixture(&notary, BODY_INJECT, 1);
        let att_c = ZkOracleAttestation {
            presentation: inj.clone(),
            zk_injection: None,
            tlsn_presentation: None,
            cfg_cert: prove_cfg_compact(BODY_INJECT.as_bytes()).unwrap(),
            field_span: span_in(&inj, b"{{system}}"),
            content_commit: content_commitment(BODY_INJECT.as_bytes()),
        };
        assert_eq!(verify_zkoracle(&att_c, &cfg), Err(ZkOracleError::Injection));
    }

    /// **THE KILLER SPLICE — the cross-leg weld.** An attestation whose evidence (cfg cert,
    /// field span, content commitment) is about body A, stapled onto an AUTHENTIC session
    /// for a DIFFERENT body B. Pre-weld the three legs were about independent objects and
    /// such a mix composed to ACCEPT; the shared commitment now REFUSES it
    /// (`CrossLegMismatch`) — the legs must be about ONE response.
    #[test]
    fn cross_leg_splice_is_refused() {
        let notary = FixtureNotary::from_seed(&[99u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());

        // Body A — a genuine benign attestation (field `hello`).
        let body_a = BODY;
        let pres_a = build_anthropic_fixture(&notary, body_a, 100);
        let genuine = prove_zkoracle(pres_a, b"hello".to_vec(), &cfg)
            .expect("genuine single-request attestation");
        verify_zkoracle(&genuine, &cfg).expect("the genuine attestation accepts");

        // Body B — a DIFFERENT authentic session (validly signed by the SAME notary).
        let body_b = r#"{"id":"msg_B","type":"message","role":"assistant","content":[{"type":"text","text":"world"}]}"#;
        let pres_b = build_anthropic_fixture(&notary, body_b, 200);

        // THE SPLICE: authentic session for B, but the well-formed cert + injection field +
        // content commitment are body A's (from the genuine attestation).
        let spliced = ZkOracleAttestation {
            presentation: pres_b.clone(),
            ..genuine.clone()
        };

        // REGRESSION DIRECTION — pre-weld each leg was independently satisfiable, so the
        // composition ACCEPTED: the session is authentic (B) …
        let session_b =
            verify_endpoint_presentation(&pres_b, &cfg).expect("B is an authentic session");
        // … a well-formed cert exists for B's body …
        assert!(
            verify_cfg_compact(
                &prove_cfg_compact(&session_b.response_body).unwrap(),
                &session_b.response_body
            )
            .is_ok()
        );
        // … and a benign field is injection-free (the pre-weld FREE injection object).
        assert!(injection_free(b"hello"));
        // Three green legs about DIFFERENT bodies — the pre-weld accept.

        // POST-WELD: the shared commitment binds them to ONE response. Recomputing it over
        // the authentic body (B) disagrees with the spliced (A's) commitment → REFUSED.
        assert_eq!(
            verify_zkoracle(&spliced, &cfg),
            Err(ZkOracleError::CrossLegMismatch)
        );
    }

    /// **The unbound-injection splice — the concrete pre-weld gap.** Pre-weld the injection
    /// leg ran over a FREE field, so an authentic + well-formed session whose real content
    /// INJECTS could be certified "injection-free" by supplying a benign standalone field.
    /// Post-weld the field is a committed substring of the authenticated body, so the real
    /// `{{`-bearing content is what the leg reads → REFUSED.
    #[test]
    fn unbound_injection_field_splice_now_refused() {
        let notary = FixtureNotary::from_seed(&[123u8; 32]);
        let cfg = AnthropicConfig::new(notary.verifying_key());
        let inj = build_anthropic_fixture(&notary, BODY_INJECT, 1);

        // Pre-weld the free benign field passed leg 3 while the authenticated content
        // injects — the false "injection-free" certification the weld closes.
        assert!(injection_free(b"hello world")); // a benign FREE field (pre-weld object)
        let body = body_of(&inj);
        assert!(!injection_free(&body)); // but the authenticated content injects

        // Post-weld: the committed span reads the authenticated `{{system}}` field.
        let att = ZkOracleAttestation {
            presentation: inj.clone(),
            zk_injection: None,
            tlsn_presentation: None,
            cfg_cert: prove_cfg_compact(&body).unwrap(),
            field_span: span_in(&inj, b"{{system}}"),
            content_commit: content_commitment(&body),
        };
        assert_eq!(verify_zkoracle(&att, &cfg), Err(ZkOracleError::Injection));
    }

    /// An out-of-range field span (evidence about a longer body) is refused by the weld.
    #[test]
    fn out_of_range_field_span_is_refused() {
        let (_n, cfg, pres) = setup();
        let body = body_of(&pres);
        let att = ZkOracleAttestation {
            presentation: pres,
            zk_injection: None,
            tlsn_presentation: None,
            cfg_cert: prove_cfg_compact(&body).unwrap(),
            field_span: FieldSpan {
                offset: body.len(),
                len: 8,
            },
            content_commit: content_commitment(&body),
        };
        assert_eq!(
            verify_zkoracle(&att, &cfg),
            Err(ZkOracleError::CrossLegMismatch)
        );
    }
}
