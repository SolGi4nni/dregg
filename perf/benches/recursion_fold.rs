//! Criterion bench: RECURSIVE AGGREGATION FOLD COST.
//!
//! Times the bundle-tree fold — the Poseidon2 compress-chain that recursively folds
//! N child digests into ONE aggregate root — proven + verified through the Lean-emitted
//! `bundle_tree_fold_descriptor` (law #1) via the IR-v2 multi-table batch STARK (the chip
//! table commits the compress chain). This is the aggregation fold the joint-turn / bundle
//! aggregation pays to collapse a fan-out of per-participant digests into one:
//!
//!   * `build_tree_fold_trace(N)` — build the compress-chain witness over N leaves.
//!   * `prove_tree_fold_v2`       — prove the chain satisfies the descriptor.
//!   * `verify_tree_fold_v2`      — the prover-free fold verify.
//!
//! The fold cost scales with the bundle fan-out N (the chain length → trace rows →
//! degree). Each proof is independently VERIFIED before the verify leg is timed.
//!
//! SMOKE (default): fold 2 leaves. FULL (`PERF_FULL=1`): the 2/8/32/128 fan-out ladder.
//!
//! Run: `cargo bench -p dregg-perf --bench recursion_fold`
//! Persvati capture: `PERF_FULL=1 cargo bench -p dregg-perf --bench recursion_fold`

use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::bilateral_aggregation_air::{
    build_tree_fold_trace, prove_tree_fold_v2, verify_tree_fold_v2,
};
use dregg_perf::{fold_digests, fold_sizes, regime};

/// PROVE: fold N child digests into one aggregate root through the descriptor batch STARK.
fn bench_fold_prove(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("recursion_fold_prove/{}", regime()));
    // Fold proving is seconds-scale; keep the sample count modest.
    group.sample_size(10);
    for n in fold_sizes() {
        let (trace, pi) = build_tree_fold_trace(&fold_digests(n));
        group.bench_with_input(BenchmarkId::from_parameter(format!("{n}_leaves")), &n, |b, _| {
            b.iter(|| {
                let proof =
                    prove_tree_fold_v2(black_box(&trace), black_box(&pi)).expect("fold must prove");
                black_box(proof);
            });
        });
    }
    group.finish();
}

/// VERIFY: the prover-free aggregate-fold verify (the light side a verifier pays).
fn bench_fold_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("recursion_fold_verify/{}", regime()));
    for n in fold_sizes() {
        let (trace, pi) = build_tree_fold_trace(&fold_digests(n));
        let proof = prove_tree_fold_v2(&trace, &pi).expect("fold must prove");
        verify_tree_fold_v2(&proof, &pi).expect("fold proof must verify");
        group.bench_with_input(BenchmarkId::from_parameter(format!("{n}_leaves")), &n, |b, _| {
            b.iter(|| {
                verify_tree_fold_v2(black_box(&proof), black_box(&pi))
                    .expect("fold proof must verify");
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_fold_prove, bench_fold_verify);
criterion_main!(benches);
