use criterion::{Criterion, black_box, criterion_group, criterion_main};
use pyana_wire::codec;
use pyana_wire::message::{AuthorizationRequest, PROTOCOL_VERSION, WireMessage};

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
    use pyana_wire::message::{PublicKey, Signature};
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

// =============================================================================
// STARK proof verification over wire (end-to-end simulation)
// =============================================================================

fn bench_stark_over_wire(c: &mut Criterion) {
    use pyana_circuit::dsl::descriptors::merkle_poseidon2_circuit;
    use pyana_circuit::dsl::membership::prove_membership_dsl;
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::stark::{self, proof_to_bytes};

    // Generate a real STARK proof using the Poseidon2-based membership circuit
    // (replaces the deprecated MerkleStarkAir which uses a linear hash binding).
    let leaf = BabyBear::new(12345);
    let siblings: Vec<[BabyBear; 3]> = vec![
        [BabyBear::new(100), BabyBear::new(200), BabyBear::new(300)],
        [BabyBear::new(400), BabyBear::new(500), BabyBear::new(600)],
        [BabyBear::new(700), BabyBear::new(800), BabyBear::new(900)],
        [
            BabyBear::new(1000),
            BabyBear::new(1100),
            BabyBear::new(1200),
        ],
    ];
    let positions: Vec<u8> = vec![0, 1, 2, 3];
    let proof = prove_membership_dsl(leaf, &siblings, &positions)
        .expect("bench proof generation must succeed");
    let proof_bytes = proof_to_bytes(&proof);

    // Capture the circuit and public inputs for the verify step.
    let circuit = merkle_poseidon2_circuit();
    let root = proof.public_inputs[1];
    let public_inputs = vec![leaf, BabyBear::new(root)];

    // Wrap in a WireMessage
    let msg = WireMessage::PresentToken {
        proof: proof_bytes.clone(),
        request: AuthorizationRequest::new("api/v1/data", "read", "bob@partner.com"),
        federation_root: [0x22; 32],
    };

    c.bench_function("wire_stark_encode_decode_verify", |b| {
        b.iter(|| {
            // Encode
            let frame = codec::encode(&msg).unwrap();

            // Decode
            let decoded = codec::decode(&frame[4..]).unwrap();

            // Extract proof and verify STARK
            if let WireMessage::PresentToken { proof: _, .. } = &decoded {
                black_box(stark::verify(&circuit, &proof, &public_inputs).unwrap());
            }
        });
    });

    // Just the wire overhead (no STARK verify)
    c.bench_function("wire_encode_decode_roundtrip_24k", |b| {
        b.iter(|| {
            let frame = codec::encode(&msg).unwrap();
            let decoded = codec::decode(&frame[4..]).unwrap();
            black_box(decoded);
        });
    });
}

criterion_group!(
    benches,
    bench_encode_decode,
    bench_throughput,
    bench_stark_over_wire,
);
criterion_main!(benches);
