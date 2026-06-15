//! Criterion bench: CANONICAL CELL COMMITMENT.
//!
//! Times the canonical state-commitment functions a turn computes for every
//! touched cell:
//!   * `compute_canonical_state_commitment` — the v8 canonical commitment.
//!   * `compute_canonical_state_commitment_v9` — the v9 rotated-limbs commitment
//!     (the rotation long pole the umem / executor-state-bridge path drives).
//!
//! Both are Poseidon2-sponge over the cell state, microseconds-scale; the same
//! populated cell is used SMOKE and FULL.
//!
//! Run: `cargo bench -p dregg-perf --bench commitment`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_cell::commitment::{
    compute_canonical_state_commitment, compute_canonical_state_commitment_v9,
};
use dregg_perf::{commitment_cell, regime, v9_context};

fn bench_commitment(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("commitment/{}", regime()));
    let cell = commitment_cell();
    let ctx = v9_context();

    group.bench_function("canonical_v8", |b| {
        b.iter(|| {
            let commit = compute_canonical_state_commitment(black_box(&cell));
            black_box(commit);
        });
    });

    group.bench_function("canonical_v9_rotated", |b| {
        b.iter(|| {
            let commit = compute_canonical_state_commitment_v9(black_box(&cell), black_box(&ctx));
            black_box(commit);
        });
    });

    group.finish();
}

criterion_group!(benches, bench_commitment);
criterion_main!(benches);
