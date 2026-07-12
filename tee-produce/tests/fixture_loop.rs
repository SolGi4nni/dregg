//! The produce→transport→verify loop, driven end-to-end by the REAL captured
//! Nitro document over a real byte stream (TCP loopback stands in for vsock —
//! the protocol is stream-agnostic on purpose). No enclave anywhere: the
//! fixture backend replays the one genuine live-enclave capture, and the REAL
//! verifier (`dregg-tee-verify`: COSE sig + chain to the pinned AWS root)
//! authenticates what came over the wire.
#![cfg(feature = "fixture-backend")]

use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::thread;

use dregg_cell::predicate::{PredicateInput, WitnessedPredicateVerifier};
use dregg_cell::tee_attest::{TeeQuoteKind, TeeWitnessedPredicateVerifier, encode_tee_proof};
use dregg_tee_produce::{
    FIXTURE_REPORT_DATA, FixtureBackend, QuoteError, request_quote, serve_quotes,
};
use dregg_tee_verify::{NitroVerifier, verify_nitro_core};

/// Serve `FixtureBackend` on a loopback listener; return the connect address.
fn spawn_fixture_server() -> std::net::SocketAddr {
    let listener = TcpListener::bind("127.0.0.1:0").expect("bind loopback");
    let addr = listener.local_addr().unwrap();
    thread::spawn(move || {
        for stream in listener.incoming().flatten() {
            let reader = stream.try_clone().expect("clone stream");
            let _ = serve_quotes(reader, stream, &FixtureBackend);
        }
    });
    addr
}

#[test]
fn the_fixture_loop_produces_a_document_the_real_verifier_accepts() {
    let addr = spawn_fixture_server();
    let mut stream = TcpStream::connect(addr).expect("connect");

    // Host side: request a quote binding the session commitment.
    let document =
        request_quote(&mut stream, FIXTURE_REPORT_DATA).expect("the captured doc comes back");

    // The REAL verifier authenticates the transported bytes: COSE signature +
    // X.509 chain to the pinned AWS Nitro root, claims extracted.
    let (claims, _ts) = verify_nitro_core(&document).expect("genuine vendor-signed document");
    assert_eq!(
        claims.report_data, FIXTURE_REPORT_DATA,
        "the quote binds exactly the requested commitment"
    );

    // And it rides the dregg predicate rail exactly as a live quote would.
    let rail = TeeWitnessedPredicateVerifier::with_verifier(Arc::new(
        NitroVerifier::without_freshness(), // captured fixture: crypto-only, deterministic forever
    ));
    let proof = encode_tee_proof(TeeQuoteKind::AwsNitro, &document);
    rail.verify(
        &claims.measurement,
        &PredicateInput::Slot(&FIXTURE_REPORT_DATA),
        &proof,
    )
    .expect("the transported quote is accepted by the rail");

    // A tampered byte in the transported document is refused by the verifier.
    let mut tampered = document.clone();
    let mid = tampered.len() / 2;
    tampered[mid] ^= 0xFF;
    assert!(
        verify_nitro_core(&tampered).is_err(),
        "a tampered transported document must not verify"
    );
}

#[test]
fn the_fixture_backend_refuses_a_commitment_it_did_not_really_attest() {
    let addr = spawn_fixture_server();
    let mut stream = TcpStream::connect(addr).expect("connect");

    // The fixture can only replay the [0xAB; 32]-bound capture: any other
    // commitment is refused server-side — no document is ever served whose
    // report_data does not match the request.
    let err = request_quote(&mut stream, [0x11u8; 32]).unwrap_err();
    assert!(
        matches!(err, QuoteError::Refused(ref e) if e.contains("fail-closed")),
        "got {err:?}"
    );
}
