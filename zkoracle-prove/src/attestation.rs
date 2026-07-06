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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
#[derive(Clone, Debug)]
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
}

/// The verified output: the authenticated session (server + response body) once all three
/// legs pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedZkOracle {
    /// The authenticated Anthropic session (server, time, response body).
    pub session: AuthenticSession,
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
pub fn verify_zkoracle(
    att: &ZkOracleAttestation,
    config: &EndpointConfig,
) -> Result<VerifiedZkOracle, ZkOracleError> {
    // Leg 1 — authentic → the authenticated response body.
    let session = verify_endpoint_presentation(&att.presentation, config)
        .map_err(ZkOracleError::NotAuthentic)?;

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

    Ok(VerifiedZkOracle { session })
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
