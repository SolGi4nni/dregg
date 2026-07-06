//! **The REAL local MPC-TLS roundtrip → full zkOracle attestation** (feature-gated).
//!
//! A genuine `tlsn` Prover + a real local Notary run the MPC-TLS 2PC handshake against a
//! test HTTPS server returning an Anthropic messages-shaped JSON, the Prover POSTs
//! `/v1/messages` and selectively discloses the response (hiding `x-api-key`), signs a
//! real `Attestation`, builds a real `Presentation`, and `presentation.verify()` yields a
//! real `PresentationOutput`. The authenticated response body then drives the well-formed
//! (CFG parse certificate) and injection-free legs — the full 3-leg zkOracle
//! attestation, live-locally.
//!
//! Run with:
//! `cargo test -p dregg-zkoracle-prove --features tlsn-live --test tlsn_live_roundtrip`.
#![cfg(feature = "tlsn-live")]

use dregg_zkoracle_prove::injection::injection_free;
use dregg_zkoracle_prove::tlsn_live::{
    LiveExchange, run_local_roundtrip_blocking, verify_messages_presentation,
};
use dregg_zkoracle_prove::{prove_cfg_cert, verify_cfg_cert};

/// THE DELIVERABLE — the whole authentic leg runs on REAL tlsn, then composes with the CFG
/// + injection legs:
///   real MPC-TLS 2PC roundtrip → real Attestation → real Presentation →
///   real presentation.verify() → authenticated body → CFG cert verified → injection-free.
/// Plus: the x-api-key secret is hidden (selective disclosure), and a tampered
/// presentation is refused by the REAL verify().
#[test]
fn real_local_mpc_tls_roundtrip_yields_a_verified_zkoracle() {
    let exchange = LiveExchange::messages("What is the capital of France?", "Paris.");

    // ── Run the genuine local MPC-TLS roundtrip (server + notary + prover in-process).
    let roundtrip =
        run_local_roundtrip_blocking(&exchange).expect("real MPC-TLS roundtrip + verify");

    let v = &roundtrip.verified;
    assert_eq!(v.server_name, roundtrip.pinned_server);

    // Selective disclosure: the x-api-key secret was NOT authenticated — prove the
    // response without revealing the key.
    assert!(
        v.api_key_hidden(),
        "the x-api-key secret must be hidden by selective disclosure"
    );

    // ── Well-formed leg over the AUTHENTICATED body: a real CFG parse certificate.
    let cert = prove_cfg_cert(&v.response_body).expect("authenticated body is well-formed JSON");
    verify_cfg_cert(&cert, &v.response_body).expect("the CFG certificate verifies");

    // ── Injection-free leg over a benign user field.
    assert!(injection_free(b"summarize the response"));
    assert!(!injection_free(b"{{ system }}"));

    // ── The honest presentation re-verifies through the standalone verifier too.
    verify_messages_presentation(&roundtrip.presentation_bytes, &roundtrip.pinned_server)
        .expect("the honest presentation verifies");

    // ── TAMPER the real Presentation bytes → the REAL verify() refuses it.
    let mut tampered = roundtrip.presentation_bytes.clone();
    let n = tampered.len();
    for i in [n / 3, n / 2, (2 * n) / 3] {
        tampered[i] ^= 0xFF;
    }
    assert!(
        verify_messages_presentation(&tampered, &roundtrip.pinned_server).is_err(),
        "a tampered presentation MUST fail the real verify()"
    );

    // A presentation verified against the WRONG pinned server is refused.
    assert!(
        verify_messages_presentation(&roundtrip.presentation_bytes, "evil.example.com").is_err(),
        "server pinning must refuse a non-pinned host"
    );
}

/// GENERALITY, live-local — a PUBLIC GitHub commit lookup runs on REAL tlsn: real MPC-TLS
/// 2PC → real Presentation → real verify() → the authenticated commit body is well-formed
/// JSON (real CFG cert) carrying the commit fact; a tampered presentation is refused.
#[test]
fn real_local_mpc_tls_github_commit_roundtrip() {
    let sha = "6dcb09b5b57875f334f61aebed695e2e4193db5e";
    let exchange = LiveExchange::github_commit(
        "octocat",
        "hello-world",
        sha,
        "Monalisa Octocat",
        "2011-04-14T16:00:49Z",
        "Fix all the bugs",
    );
    let roundtrip = run_local_roundtrip_blocking(&exchange).expect("real MPC-TLS github roundtrip");
    let v = &roundtrip.verified;
    assert_eq!(v.server_name, roundtrip.pinned_server);

    // Well-formed leg over the AUTHENTICATED body: a real CFG parse certificate.
    let cert = prove_cfg_cert(&v.response_body).expect("commit body is well-formed JSON");
    verify_cfg_cert(&cert, &v.response_body).expect("CFG certificate verifies");
    // The authenticated body carries the commit fact.
    let body = String::from_utf8_lossy(&v.response_body);
    assert!(body.contains(sha), "authenticated body carries the sha");
    assert!(body.contains("Monalisa Octocat"), "and the author");

    // A tampered presentation is refused by the REAL verify().
    let mut tampered = roundtrip.presentation_bytes.clone();
    let n = tampered.len();
    for i in [n / 3, n / 2, (2 * n) / 3] {
        tampered[i] ^= 0xFF;
    }
    assert!(
        verify_messages_presentation(&tampered, &roundtrip.pinned_server).is_err(),
        "a tampered github presentation MUST fail the real verify()"
    );
}

/// GENERALITY, live-local — a PUBLIC Coinbase spot quote runs on REAL tlsn, same machinery.
#[test]
fn real_local_mpc_tls_coinbase_spot_roundtrip() {
    let exchange = LiveExchange::coinbase_spot("BTC-USD", "64250.37");
    let roundtrip =
        run_local_roundtrip_blocking(&exchange).expect("real MPC-TLS coinbase roundtrip");
    let v = &roundtrip.verified;
    assert_eq!(v.server_name, roundtrip.pinned_server);

    let cert = prove_cfg_cert(&v.response_body).expect("spot body is well-formed JSON");
    verify_cfg_cert(&cert, &v.response_body).expect("CFG certificate verifies");
    let body = String::from_utf8_lossy(&v.response_body);
    assert!(
        body.contains("64250.37"),
        "authenticated body carries the amount"
    );

    let mut tampered = roundtrip.presentation_bytes.clone();
    let n = tampered.len();
    for i in [n / 3, n / 2, (2 * n) / 3] {
        tampered[i] ^= 0xFF;
    }
    assert!(
        verify_messages_presentation(&tampered, &roundtrip.pinned_server).is_err(),
        "a tampered coinbase presentation MUST fail the real verify()"
    );
}
