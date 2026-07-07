use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_wire::codec;
use dregg_wire::message::{AuthorizationRequest, PROTOCOL_VERSION, WireMessage};

// =============================================================================
// Message encoding/decoding benchmarks
// =============================================================================

fn make_hello_message() -> WireMessage {
    WireMessage::Hello {
        node_id: [0xAB; 32],
        node_name: "test-silo-alpha".into(),
        protocol_version: PROTOCOL_VERSION,
        capabilities: vec!["present".into(), "revoke".into(), "sync".into()],
    }
}

fn make_present_token_message() -> WireMessage {
    WireMessage::PresentToken {
        proof: vec![0xDE; 24 * 1024], // ~24 KiB simulated STARK proof
        request: AuthorizationRequest::new("api/v1/users", "read", "alice@acme.com"),
        federation_root: [0x11; 32],
    }
}

fn make_submit_revocation_message() -> WireMessage {
    use dregg_wire::message::{PublicKey, Signature};
    WireMessage::SubmitRevocation {
        token_id: "revoked-token-42".into(),
        authority: PublicKey([0x42; 32]),
        authority_sig: Signature([0xFF; 64]),
        nonce: [0xAB; 16],
        timestamp: 1700000000,
    }
}

fn bench_encode_decode(c: &mut Criterion) {
    let mut group = c.benchmark_group("wire_codec");

    // Hello message (small)
    let hello = make_hello_message();
    let hello_bytes = codec::encode(&hello).unwrap();
    group.bench_function("encode_hello", |b| {
        b.iter(|| black_box(codec::encode(&hello).unwrap()));
    });
    group.bench_function("decode_hello", |b| {
        b.iter(|| black_box(codec::decode(&hello_bytes[4..]).unwrap()));
    });

    // PresentToken message (large, ~24 KiB proof)
    let present = make_present_token_message();
    let present_bytes = codec::encode(&present).unwrap();
    group.bench_function("encode_present_24k", |b| {
        b.iter(|| black_box(codec::encode(&present).unwrap()));
    });
    group.bench_function("decode_present_24k", |b| {
        b.iter(|| black_box(codec::decode(&present_bytes[4..]).unwrap()));
    });

    // Revocation message (medium)
    let revoke = make_submit_revocation_message();
    let revoke_bytes = codec::encode(&revoke).unwrap();
    group.bench_function("encode_revocation", |b| {
        b.iter(|| black_box(codec::encode(&revoke).unwrap()));
    });
    group.bench_function("decode_revocation", |b| {
        b.iter(|| black_box(codec::decode(&revoke_bytes[4..]).unwrap()));
    });

    // Report message sizes
    eprintln!("  [msg_size] Hello: {} bytes", hello_bytes.len());
    eprintln!(
        "  [msg_size] PresentToken(24K proof): {} bytes",
        present_bytes.len()
    );
    eprintln!("  [msg_size] Revocation: {} bytes", revoke_bytes.len());

    group.finish();
}

// =============================================================================
// Message throughput benchmarks (batch encode/decode)
// =============================================================================

fn bench_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("wire_throughput");

    // Batch of 100 hello messages
    let hello = make_hello_message();
    group.bench_function("encode_100_hello", |b| {
        b.iter(|| {
            for _ in 0..100 {
                black_box(codec::encode(&hello).unwrap());
            }
        });
    });

    // Batch of 10 present-token messages
    let present = make_present_token_message();
    group.bench_function("encode_10_present", |b| {
        b.iter(|| {
            for _ in 0..10 {
                black_box(codec::encode(&present).unwrap());
            }
        });
    });

    group.finish();
}

// NOTE: the end-to-end "STARK proof verification over wire" benchmark that used
// to live here was retired with the legacy `dregg_circuit` STARK engine. The
// wire codec is still exercised against a realistic ~24 KiB proof payload above
// (`encode_present_24k` / `decode_present_24k`).

criterion_group!(benches, bench_encode_decode, bench_throughput,);
criterion_main!(benches);
