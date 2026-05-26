use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::field::BabyBear;
use dregg_circuit::ivc::{IvcBuilder, create_test_chain, prove_ivc, verify_ivc};
use dregg_circuit::poseidon2::{Poseidon2State, hash_4_to_1, hash_many};
use dregg_circuit::stark::{self, MerkleStarkAir, generate_merkle_trace, proof_to_bytes};

// =============================================================================
// STARK proof generation benchmarks
// =============================================================================

fn bench_stark_prove(c: &mut Criterion) {
    let mut group = c.benchmark_group("stark_prove");

    // Vary trace sizes: 4, 8, 16, 32 rows (must be power of 2 and >= 2 levels)
    for &depth in &[4, 8, 16, 32] {
        let siblings: Vec<[u32; 3]> = (0..depth)
            .map(|i| {
                [
                    (i * 100 + 10) as u32,
                    (i * 100 + 20) as u32,
                    (i * 100 + 30) as u32,
                ]
            })
            .collect();
        let positions: Vec<u32> = (0..depth).map(|i| (i % 4) as u32).collect();
        let (trace, public_inputs) = generate_merkle_trace(12345, &siblings, &positions);

        group.bench_with_input(
            BenchmarkId::new("rows", trace.len()),
            &(trace.clone(), public_inputs.clone()),
            |b, (trace, pi)| {
                let air = MerkleStarkAir;
                b.iter(|| {
                    black_box(stark::prove(&air, trace, pi));
                });
            },
        );
    }

    group.finish();
}

fn bench_stark_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("stark_verify");

    for &depth in &[4, 8, 16, 32] {
        let siblings: Vec<[u32; 3]> = (0..depth)
            .map(|i| {
                [
                    (i * 100 + 10) as u32,
                    (i * 100 + 20) as u32,
                    (i * 100 + 30) as u32,
                ]
            })
            .collect();
        let positions: Vec<u32> = (0..depth).map(|i| (i % 4) as u32).collect();
        let (trace, public_inputs) = generate_merkle_trace(12345, &siblings, &positions);
        let air = MerkleStarkAir;
        let proof = stark::prove(&air, &trace, &public_inputs);

        group.bench_with_input(
            BenchmarkId::new("rows", trace.len()),
            &(proof, public_inputs.clone()),
            |b, (proof, pi)| {
                let air = MerkleStarkAir;
                b.iter(|| {
                    black_box(stark::verify(&air, proof, pi).unwrap());
                });
            },
        );
    }

    group.finish();
}

fn bench_stark_proof_size(c: &mut Criterion) {
    // This is a "benchmark" that just reports proof sizes.
    // We use criterion's iteration to get stable numbers.
    let mut group = c.benchmark_group("stark_proof_size");

    for &depth in &[4, 8, 16, 32] {
        let siblings: Vec<[u32; 3]> = (0..depth)
            .map(|i| {
                [
                    (i * 100 + 10) as u32,
                    (i * 100 + 20) as u32,
                    (i * 100 + 30) as u32,
                ]
            })
            .collect();
        let positions: Vec<u32> = (0..depth).map(|i| (i % 4) as u32).collect();
        let (trace, public_inputs) = generate_merkle_trace(12345, &siblings, &positions);
        let air = MerkleStarkAir;
        let proof = stark::prove(&air, &trace, &public_inputs);
        let bytes = proof_to_bytes(&proof);

        group.bench_with_input(
            BenchmarkId::new("serialize_rows", trace.len()),
            &proof,
            |b, proof| {
                b.iter(|| {
                    black_box(proof_to_bytes(proof));
                });
            },
        );

        // Print the proof size (once, during setup)
        eprintln!(
            "  [proof_size] depth={} rows={} size={} bytes ({:.1} KiB)",
            depth,
            trace.len(),
            bytes.len(),
            bytes.len() as f64 / 1024.0
        );
    }

    group.finish();
}

// =============================================================================
// Poseidon2 hash benchmarks
// =============================================================================

fn bench_poseidon2_hash(c: &mut Criterion) {
    let mut group = c.benchmark_group("poseidon2");

    // Single hash (4-to-1)
    let input = [
        BabyBear::new(1),
        BabyBear::new(2),
        BabyBear::new(3),
        BabyBear::new(4),
    ];
    group.bench_function("hash_4_to_1_single", |b| {
        b.iter(|| black_box(hash_4_to_1(&input)));
    });

    // 100 hashes
    group.bench_function("hash_4_to_1_x100", |b| {
        b.iter(|| {
            let mut acc = BabyBear::ZERO;
            for i in 0..100u32 {
                let inp = [
                    BabyBear::new(i),
                    BabyBear::new(i + 1),
                    BabyBear::new(i + 2),
                    BabyBear::new(i + 3),
                ];
                acc = hash_4_to_1(&inp);
            }
            black_box(acc)
        });
    });

    // 1000 hashes
    group.bench_function("hash_4_to_1_x1000", |b| {
        b.iter(|| {
            let mut acc = BabyBear::ZERO;
            for i in 0..1000u32 {
                let inp = [
                    BabyBear::new(i),
                    BabyBear::new(i + 1),
                    BabyBear::new(i + 2),
                    BabyBear::new(i + 3),
                ];
                acc = hash_4_to_1(&inp);
            }
            black_box(acc)
        });
    });

    // hash_many with varying input sizes
    let inputs_8: Vec<BabyBear> = (0..8).map(|i| BabyBear::new(i)).collect();
    let inputs_32: Vec<BabyBear> = (0..32).map(|i| BabyBear::new(i)).collect();
    group.bench_function("hash_many_8_elements", |b| {
        b.iter(|| black_box(hash_many(&inputs_8)));
    });
    group.bench_function("hash_many_32_elements", |b| {
        b.iter(|| black_box(hash_many(&inputs_32)));
    });

    // Poseidon2 permutation (raw)
    group.bench_function("permutation", |b| {
        let mut state = Poseidon2State::from_elements(&[
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
        ]);
        b.iter(|| {
            state.permute();
            black_box(&state);
        });
    });

    group.finish();
}

// =============================================================================
// BabyBear field operation benchmarks
// =============================================================================

fn bench_field_ops(c: &mut Criterion) {
    let mut group = c.benchmark_group("babybear_field");

    let a = BabyBear::new(1_234_567_890);
    let b = BabyBear::new(987_654_321);

    group.bench_function("add", |b_iter| {
        b_iter.iter(|| black_box(a + b));
    });

    group.bench_function("mul", |b_iter| {
        b_iter.iter(|| black_box(a * b));
    });

    group.bench_function("inverse", |b_iter| {
        b_iter.iter(|| black_box(a.inverse()));
    });

    group.bench_function("pow_7", |b_iter| {
        b_iter.iter(|| black_box(a.pow(7)));
    });

    group.bench_function("pow_large", |b_iter| {
        b_iter.iter(|| black_box(a.pow(2013265919)));
    });

    group.finish();
}

// =============================================================================
// IVC accumulation benchmarks
// =============================================================================

fn bench_ivc(c: &mut Criterion) {
    let mut group = c.benchmark_group("ivc");

    // IVC prove for varying chain lengths
    for &steps in &[1, 3, 5, 10] {
        let (initial_root, deltas) = create_test_chain(steps);
        group.bench_with_input(
            BenchmarkId::new("prove", steps),
            &(initial_root, deltas.clone()),
            |b, (root, deltas)| {
                b.iter(|| {
                    black_box(prove_ivc(*root, deltas.clone()).unwrap());
                });
            },
        );
    }

    // IVC verify
    for &steps in &[1, 5, 10] {
        let (initial_root, deltas) = create_test_chain(steps);
        let proof = prove_ivc(initial_root, deltas).unwrap();
        group.bench_with_input(
            BenchmarkId::new("verify", steps),
            &(proof, initial_root),
            |b, (proof, root)| {
                b.iter(|| {
                    black_box(verify_ivc(proof, Some(*root)));
                });
            },
        );
    }

    // Single accumulation step (incremental IVC)
    {
        let (initial_root, deltas) = create_test_chain(5);
        let mut builder = IvcBuilder::new(initial_root);
        // Add 4 steps, then benchmark adding the 5th
        for delta in &deltas[..4] {
            builder.add_fold(delta.clone()).unwrap();
        }
        let last_delta = deltas[4].clone();
        group.bench_function("single_step", |b| {
            b.iter(|| {
                let mut b2 = IvcBuilder::new(initial_root);
                for d in &deltas[..4] {
                    b2.add_fold(d.clone()).unwrap();
                }
                black_box(b2.add_fold(last_delta.clone()).unwrap());
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_stark_prove,
    bench_stark_verify,
    bench_stark_proof_size,
    bench_poseidon2_hash,
    bench_field_ops,
    bench_ivc,
);
criterion_main!(benches);
