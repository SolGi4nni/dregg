//! Criterion bench: THE ROTATED MULTI-TABLE CIRCUIT, PROVE + VERIFY PER EFFECT-COHORT.
//!
//! Times the EPOCH IR-v2 multi-table batch STARK (`descriptor_ir2::prove_vm_descriptor2`
//! / `verify_vm_descriptor2`) — the LIVE rotated commit circuit under the `recursion`
//! default — across the distinct effect-cohort *table shapes*:
//!
//!   * `transfer_5table` — the graduated `transferVmDescriptor2` (main + poseidon2-chip +
//!     range + memory + map-ops) over a REAL transfer trace; the headline per-turn circuit cost.
//!   * `map_write_chip` — one in-place sorted-Poseidon2 write riding the chip bus (a boundary
//!     map-op; pays the chip table).
//!   * `umem_write_read_nochip` — the SAME write+read as universal-memory ops (the ONE Blum
//!     multiset); commits NO chip table, zero intra-proof hashing.
//!   * `absent_chip` — a sorted-Poseidon2 NON-membership (the boundary-gap leg; pays the chip).
//!
//! These are the four distinct table-set shapes the per-effect rotated descriptors descend
//! from (chip-bearing map ops vs the no-chip universal-memory multiset). Each proof is
//! independently VERIFIED before the verify leg is timed, so the numbers are over real
//! proofs through the production `ir2_config`. The statements mirror exactly what
//! `circuit/tests/effect_vm_ir2_{validate,size_measure}.rs` prove.
//!
//! SMOKE (default): the transfer cohort only. FULL (`PERF_FULL=1`): all four shapes.
//!
//! Run: `cargo bench -p dregg-perf --bench cohort_circuit`
//! Persvati capture: `PERF_FULL=1 cargo bench -p dregg-perf --bench cohort_circuit`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_circuit::descriptor_ir2::verify_vm_descriptor2;
use dregg_perf::{cohorts, prove_cohort, regime};

/// PROVE: the multi-table batch STARK per cohort (the real rotated circuit prove cost).
fn bench_cohort_prove(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("cohort_prove/{}", regime()));
    // Multi-table proving is seconds-scale; keep the sample count modest.
    group.sample_size(10);
    for cohort in cohorts() {
        group.bench_function(cohort.name, |b| {
            b.iter(|| {
                let proof = prove_cohort(black_box(&cohort));
                black_box(proof);
            });
        });
    }
    group.finish();
}

/// VERIFY: the prover-free multi-table batch verifier per cohort (the light side a
/// verifier / light-client pays).
fn bench_cohort_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("cohort_verify/{}", regime()));
    for cohort in cohorts() {
        let proof = prove_cohort(&cohort);
        // Sanity: the cohort proof must verify before it is timed.
        verify_vm_descriptor2(&cohort.desc, &proof, &cohort.pis)
            .expect("cohort proof must verify");
        group.bench_function(cohort.name, |b| {
            b.iter(|| {
                verify_vm_descriptor2(black_box(&cohort.desc), black_box(&proof), &cohort.pis)
                    .expect("cohort proof must verify");
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_cohort_prove, bench_cohort_verify);
criterion_main!(benches);
