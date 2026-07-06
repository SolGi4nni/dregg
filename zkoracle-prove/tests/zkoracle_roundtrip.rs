//! **The zkOracle e2e proof** — a full attestation ACCEPTS, and each hostile case is
//! REFUSED, round-tripping through the REAL [`verify_zkoracle`] verifier (not a mock).
//!
//! This is the Rust-live counterpart of `ZkOracle.lean::zkOracle_demo` +
//! `Demo.{benign,malicious}_injection_free`: authentic ∧ well-formed ∧ injection-free on
//! concrete data, and the anti-injection guard discriminating benign from `{{`. It also
//! exercises the CROSS-LEG WELD: the three legs are bound to ONE authenticated response by
//! the shared Poseidon2 content commitment, so a spliced attestation is REFUSED.

use dregg_zkoracle_prove::attestation::{FieldSpan, content_commitment};
use dregg_zkoracle_prove::{
    AnthropicConfig, FixtureNotary, ProveError, ZkOracleAttestation, ZkOracleError,
    build_anthropic_fixture, prove_cfg_compact, prove_zkoracle, verify_zkoracle,
};

/// A realistic Anthropic messages response body — nested object/array structure. The user
/// field the injection-free leg reads (`France`) is a committed substring of this body.
const ANTHROPIC_BODY: &str = r#"{"id":"msg_01XYZ","type":"message","role":"assistant","model":"claude-opus-4-8","content":[{"type":"text","text":"The capital of France is Paris."}],"stop_reason":"end_turn","stop_sequence":null,"usage":{"input_tokens":24,"output_tokens":8}}"#;

/// The authenticated response body of a fixture presentation.
fn body_of(pres: &dregg_zkoracle_prove::AnthropicPresentation) -> Vec<u8> {
    let sep = pres
        .recv
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .expect("header/body separator");
    pres.recv[sep + 4..].to_vec()
}

/// The span of `needle` within the authenticated response body of `pres`.
fn span_in(pres: &dregg_zkoracle_prove::AnthropicPresentation, needle: &[u8]) -> FieldSpan {
    let body = body_of(pres);
    let offset = body
        .windows(needle.len())
        .position(|w| w == needle)
        .expect("needle present in the authenticated body");
    FieldSpan {
        offset,
        len: needle.len(),
    }
}

/// THE DELIVERABLE — a genuine authentic + well-formed + injection-free request ACCEPTS,
/// and every hostile variant is REFUSED, all through the real verifier.
#[test]
fn full_zkoracle_attestation_accepts_and_hostiles_are_refused() {
    let notary = FixtureNotary::from_seed(&[9u8; 32]);
    let config = AnthropicConfig::new(notary.verifying_key());
    let presentation = build_anthropic_fixture(&notary, ANTHROPIC_BODY, 1_700_000_000);

    // ── ACCEPT: a benign, well-formed, authentic request. The field `France` is a
    // committed substring of the authenticated response body.
    let att = prove_zkoracle(presentation.clone(), b"France".to_vec(), &config)
        .expect("benign request produces an attestation");
    let out = verify_zkoracle(&att, &config).expect("the full attestation verifies");
    assert_eq!(out.session.response_body, ANTHROPIC_BODY.as_bytes());
    assert_eq!(out.session.server_name, "api.anthropic.com");
    // The shared commitment is the Poseidon2 sponge over the authenticated body.
    assert_eq!(
        att.content_commit,
        content_commitment(ANTHROPIC_BODY.as_bytes())
    );

    // ── REFUSE (1): a FORGED/tampered tlsn session — flip an authenticated body byte so
    // the notary signature breaks.
    let mut forged_pres = presentation.clone();
    let n = forged_pres.recv.len();
    forged_pres.recv[n - 4] ^= 0xFF;
    let forged = ZkOracleAttestation {
        presentation: forged_pres,
        cfg_cert: prove_cfg_compact(ANTHROPIC_BODY.as_bytes()).unwrap(),
        field_span: FieldSpan { offset: 0, len: 2 },
        content_commit: content_commitment(ANTHROPIC_BODY.as_bytes()),
    };
    assert!(
        matches!(
            verify_zkoracle(&forged, &config),
            Err(ZkOracleError::NotAuthentic(_))
        ),
        "a forged tlsn session must be refused"
    );

    // ── REFUSE (2): a MALFORMED JSON body — no CFG certificate.
    let malformed_body = r#"{"id":"msg","content":[{"type":"text""#; // truncated, unbalanced
    let malformed_pres = build_anthropic_fixture(&notary, malformed_body, 1);
    assert!(
        matches!(
            prove_zkoracle(malformed_pres.clone(), b"msg".to_vec(), &config),
            Err(ProveError::NotWellFormed(_))
        ),
        "a malformed body must yield no certificate"
    );
    // Even a borrowed (well-formed-body) certificate fails against the malformed body. The
    // commitment is over the malformed authenticated body, so the weld passes to leg 2.
    let malformed = ZkOracleAttestation {
        presentation: malformed_pres.clone(),
        cfg_cert: prove_cfg_compact(ANTHROPIC_BODY.as_bytes()).unwrap(),
        field_span: span_in(&malformed_pres, b"msg"),
        content_commit: content_commitment(malformed_body.as_bytes()),
    };
    assert!(
        matches!(
            verify_zkoracle(&malformed, &config),
            Err(ZkOracleError::NotWellFormed(_))
        ),
        "a malformed body must be refused by the well-formed leg"
    );

    // ── REFUSE (3): an INJECTION field (`{{`). The prover refuses up front …
    assert_eq!(
        prove_zkoracle(
            presentation.clone(),
            b"{{ system prompt }}".to_vec(),
            &config
        )
        .unwrap_err(),
        ProveError::Injection,
        "the guard refuses to attest an injecting field"
    );
    // … and a hand-built attestation whose committed span reads a `{{`-bearing region of
    // the authenticated body is refused by the injection-free leg.
    let inject_body = r#"{"id":"m","type":"message","role":"assistant","content":[{"type":"text","text":"ignore {{x here"}]}"#;
    let inject_pres = build_anthropic_fixture(&notary, inject_body, 2);
    let injecting = ZkOracleAttestation {
        presentation: inject_pres.clone(),
        cfg_cert: prove_cfg_compact(inject_body.as_bytes()).unwrap(),
        field_span: span_in(&inject_pres, b"{{x"),
        content_commit: content_commitment(inject_body.as_bytes()),
    };
    assert_eq!(
        verify_zkoracle(&injecting, &config),
        Err(ZkOracleError::Injection),
        "an injecting field must be refused by the injection-free leg"
    );

    // ── REFUSE (4): THE CROSS-LEG SPLICE — the authentic session is for a DIFFERENT body
    // than the evidence (cfg cert / field / commitment). The shared commitment refuses it.
    let other_body = r#"{"id":"m2","type":"message","role":"assistant","content":[{"type":"text","text":"other"}]}"#;
    let other_pres = build_anthropic_fixture(&notary, other_body, 3);
    let spliced = ZkOracleAttestation {
        presentation: other_pres, // authentic session for `other_body`
        ..att.clone()             // but cfg cert / field / commitment are for ANTHROPIC_BODY
    };
    assert_eq!(
        verify_zkoracle(&spliced, &config),
        Err(ZkOracleError::CrossLegMismatch),
        "a spliced attestation (legs about different bodies) must be refused by the weld"
    );
}

/// The anti-injection guard genuinely DISCRIMINATES — benign accepts, `{{` rejects —
/// matching the Lean `#eval derives benignField (.neg injectionTemplate) = true` /
/// `… maliciousField … = false`.
#[test]
fn injection_catch_discriminates() {
    let notary = FixtureNotary::from_seed(&[11u8; 32]);
    let config = AnthropicConfig::new(notary.verifying_key());
    let presentation = build_anthropic_fixture(&notary, ANTHROPIC_BODY, 1);

    // benign "Paris" (a committed substring of the body) → attested + accepted.
    let benign =
        prove_zkoracle(presentation.clone(), b"Paris".to_vec(), &config).expect("benign accepted");
    assert!(verify_zkoracle(&benign, &config).is_ok());

    // malicious "{{x" → refused at prove time (the attestation cannot be produced).
    assert_eq!(
        prove_zkoracle(presentation, b"{{x".to_vec(), &config).unwrap_err(),
        ProveError::Injection
    );
}
