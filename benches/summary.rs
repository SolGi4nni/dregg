//! Performance summary: runs key operations and prints a formatted table.
//!
//! Run with: `cargo run --release --example summary` (from workspace root)
//! Or:       `cargo run --release -p dregg-bench-summary`

use std::time::{Duration, Instant};

fn time_op<F: FnMut()>(mut f: F, iterations: u32) -> Duration {
    // Warmup
    for _ in 0..3 {
        f();
    }

    let start = Instant::now();
    for _ in 0..iterations {
        f();
    }
    start.elapsed() / iterations
}

fn format_duration(d: Duration) -> String {
    let nanos = d.as_nanos();
    if nanos < 1_000 {
        format!("{} ns", nanos)
    } else if nanos < 1_000_000 {
        format!("{:.1} us", nanos as f64 / 1_000.0)
    } else if nanos < 1_000_000_000 {
        format!("{:.1} ms", nanos as f64 / 1_000_000.0)
    } else {
        format!("{:.2} s", nanos as f64 / 1_000_000_000.0)
    }
}

fn format_size(bytes: usize) -> String {
    if bytes < 1024 {
        format!("{} B", bytes)
    } else if bytes < 1024 * 1024 {
        format!("{:.1} KiB", bytes as f64 / 1024.0)
    } else {
        format!("{:.1} MiB", bytes as f64 / (1024.0 * 1024.0))
    }
}

fn main() {
    println!();
    println!("=============================================================================");
    println!("  DREGG Performance Summary");
    println!("=============================================================================");
    println!();
    println!("{:<40} | {:<12} | {:<10}", "Operation", "Time", "Size");
    println!("{:-<40}-+-{:-<12}-+-{:-<10}", "", "", "");

    // -------------------------------------------------------------------------
    // Token Operations (macaroon)
    // -------------------------------------------------------------------------
    {
        use dregg_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};

        let key = {
            let mut k = [0u8; 32];
            getrandom::fill(&mut k).unwrap();
            k
        };

        // Macaroon mint
        let d = time_op(
            || {
                let _ = MacaroonToken::mint(key, b"kid", "dregg.dev");
            },
            10_000,
        );
        println!(
            "{:<40} | {:<12} | {:<10}",
            "Macaroon mint",
            format_duration(d),
            "-"
        );

        // Macaroon verify (no caveats)
        let token = MacaroonToken::mint(key, b"kid", "dregg.dev");
        let request = AuthRequest::default();
        let d = time_op(
            || {
                let _ = token.verify(&request);
            },
            10_000,
        );
        println!(
            "{:<40} | {:<12} | {:<10}",
            "Macaroon verify (0 caveats)",
            format_duration(d),
            "-"
        );

        // Macaroon verify (5 caveats)
        let token5 = {
            let mut t: Box<dyn AuthToken> = Box::new(MacaroonToken::mint(key, b"kid", "dregg.dev"));
            for i in 0..5 {
                let att = Attenuation {
                    apps: vec![(format!("app-{i}"), "r".into())],
                    ..Default::default()
                };
                t = t.attenuate(&att).unwrap();
            }
            t
        };
        let d = time_op(
            || {
                let _ = token5.verify(&request);
            },
            10_000,
        );
        println!(
            "{:<40} | {:<12} | {:<10}",
            "Macaroon verify (5 caveats)",
            format_duration(d),
            "-"
        );

        // Token size
        let encoded = token5.to_encoded().unwrap();
        println!(
            "{:<40} | {:<12} | {:<10}",
            "Macaroon token (5 caveats)",
            "-",
            format_size(encoded.len())
        );
    }

    println!("{:-<40}-+-{:-<12}-+-{:-<10}", "", "", "");

    // -------------------------------------------------------------------------
    // STARK Proof Operations
    // -------------------------------------------------------------------------
    {
        use dregg_circuit::field::BabyBear;
        use dregg_circuit::stark::{self, MerkleStarkAir, generate_merkle_trace, proof_to_bytes};

        // 4-level Merkle membership STARK
        let siblings = [
            [100u32, 200, 300],
            [400, 500, 600],
            [700, 800, 900],
            [1000, 1100, 1200],
        ];
        let positions = [0u32, 1, 2, 3];
        let (trace, public_inputs) = generate_merkle_trace(12345, &siblings, &positions);
        let air = MerkleStarkAir;

        // STARK prove
        let d = time_op(
            || {
                let _ = stark::prove(&air, &trace, &public_inputs);
            },
            10,
        );
        let proof = stark::prove(&air, &trace, &public_inputs);
        let proof_bytes = proof_to_bytes(&proof);
        println!(
            "{:<40} | {:<12} | {:<10}",
            "STARK proof generation (4 rows)",
            format_duration(d),
            format_size(proof_bytes.len())
        );

        // STARK verify
        let d = time_op(
            || {
                let _ = stark::verify(&air, &proof, &public_inputs);
            },
            100,
        );
        println!(
            "{:<40} | {:<12} | {:<10}",
            "STARK proof verification",
            format_duration(d),
            "-"
        );

        // 8-row trace (deeper Merkle)
        let siblings8: Vec<[u32; 3]> = (0..8)
            .map(|i| {
                [
                    (i * 100 + 10) as u32,
                    (i * 100 + 20) as u32,
                    (i * 100 + 30) as u32,
                ]
            })
            .collect();
        let positions8: Vec<u32> = (0..8).map(|i| (i % 4) as u32).collect();
        let (trace8, pi8) = generate_merkle_trace(12345, &siblings8, &positions8);
        let d = time_op(
            || {
                let _ = stark::prove(&air, &trace8, &pi8);
            },
            5,
        );
        let proof8 = stark::prove(&air, &trace8, &pi8);
        let bytes8 = proof_to_bytes(&proof8);
        println!(
            "{:<40} | {:<12} | {:<10}",
            "STARK proof generation (8 rows)",
            format_duration(d),
            format_size(bytes8.len())
        );
    }

    println!("{:-<40}-+-{:-<12}-+-{:-<10}", "", "", "");

    // -------------------------------------------------------------------------
    // IVC Operations
    // -------------------------------------------------------------------------
    {
        use dregg_circuit::ivc::{create_test_chain, prove_ivc, verify_ivc};

        // IVC 5-step
        let (initial_root, deltas) = create_test_chain(5);
        let d = time_op(
            || {
                let _ = prove_ivc(initial_root, deltas.clone());
            },
            50,
        );
        let proof = prove_ivc(initial_root, deltas).unwrap();
        println!(
            "{:<40} | {:<12} | {:<10}",
            "IVC prove (5 steps)",
            format_duration(d),
            format_size(proof.proof_size_bytes())
        );

        // IVC verify
        let d = time_op(
            || {
                let _ = verify_ivc(&proof, Some(initial_root));
            },
            10_000,
        );
        println!(
            "{:<40} | {:<12} | {:<10}",
            "IVC verify",
            format_duration(d),
            "-"
        );

        // IVC 10-step
        let (initial_root10, deltas10) = create_test_chain(10);
        let d = time_op(
            || {
                let _ = prove_ivc(initial_root10, deltas10.clone());
            },
            20,
        );
        let proof10 = prove_ivc(initial_root10, deltas10).unwrap();
        println!(
            "{:<40} | {:<12} | {:<10}",
            "IVC prove (10 steps)",
            format_duration(d),
            format_size(proof10.proof_size_bytes())
        );
    }

    println!("{:-<40}-+-{:-<12}-+-{:-<10}", "", "", "");

    // -------------------------------------------------------------------------
    // Poseidon2 / Field Operations
    // -------------------------------------------------------------------------
    {
        use dregg_circuit::field::BabyBear;
        use dregg_circuit::poseidon2::hash_4_to_1;

        let input = [
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
        ];
        let d = time_op(
            || {
                let _ = hash_4_to_1(&input);
            },
            100_000,
        );
        println!(
            "{:<40} | {:<12} | {:<10}",
            "Poseidon2 hash (4-to-1)",
            format_duration(d),
            "-"
        );

        let a = BabyBear::new(1_234_567_890);
        let d = time_op(
            || {
                let _ = a.inverse();
            },
            100_000,
        );
        println!(
            "{:<40} | {:<12} | {:<10}",
            "BabyBear field inverse",
            format_duration(d),
            "-"
        );
    }

    println!("{:-<40}-+-{:-<12}-+-{:-<10}", "", "", "");

    // -------------------------------------------------------------------------
    // BLS Threshold Signatures
    // -------------------------------------------------------------------------
    {
        use hints::sign as bls_sign;
        use dregg_federation::{FederationCommittee, generate_test_committee};

        let (committee, secrets) = generate_test_committee(5, 3).unwrap();
        let msg = b"benchmark-message";

        // Partial sign
        let d = time_op(
            || {
                let _ = bls_sign(&secrets[0].secret_key, msg);
            },
            1000,
        );
        println!(
            "{:<40} | {:<12} | {:<10}",
            "BLS partial sign",
            format_duration(d),
            "-"
        );

        // Aggregate (5 signers)
        let shares: Vec<_> = secrets
            .iter()
            .map(|s| (s.index, committee.sign_share(s, msg)))
            .collect();
        let d = time_op(
            || {
                let _ = committee.aggregate(&shares, msg);
            },
            10,
        );
        let qc = committee.aggregate(&shares, msg).unwrap();
        let qc_bytes = qc.to_bytes();
        println!(
            "{:<40} | {:<12} | {:<10}",
            "BLS aggregate + SNARK (5 signers)",
            format_duration(d),
            format_size(qc_bytes.len())
        );

        // Verify aggregate
        let d = time_op(
            || {
                let _ = committee.verify(&qc, msg);
            },
            50,
        );
        println!(
            "{:<40} | {:<12} | {:<10}",
            "BLS verify_aggregate",
            format_duration(d),
            "-"
        );
    }

    println!("{:-<40}-+-{:-<12}-+-{:-<10}", "", "", "");

    // -------------------------------------------------------------------------
    // Wire Protocol
    // -------------------------------------------------------------------------
    {
        use dregg_wire::codec;
        use dregg_wire::message::{AuthorizationRequest, WireMessage};

        let msg = WireMessage::PresentToken {
            proof: vec![0xDE; 24 * 1024],
            request: AuthorizationRequest::new("api/v1/data", "read", "alice@acme.com"),
            federation_root: [0x11; 32],
        };
        let encoded = codec::encode(&msg).unwrap();

        let d = time_op(
            || {
                let _ = codec::encode(&msg);
            },
            10_000,
        );
        println!(
            "{:<40} | {:<12} | {:<10}",
            "Wire encode (24K proof msg)",
            format_duration(d),
            format_size(encoded.len())
        );

        let d = time_op(
            || {
                let _ = codec::decode(&encoded[4..]);
            },
            10_000,
        );
        println!(
            "{:<40} | {:<12} | {:<10}",
            "Wire decode (24K proof msg)",
            format_duration(d),
            "-"
        );
    }

    println!();
    println!("=============================================================================");
    println!("  All timings are per-operation averages (release build).");
    println!("  Run `cargo bench` for statistical analysis with confidence intervals.");
    println!("=============================================================================");
    println!();
}
