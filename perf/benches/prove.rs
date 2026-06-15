//! Criterion bench: TRANSFER PROVE.
//!
//! Times the LIVE proving paths for a Transfer turn:
//!   * `prove_full_turn` (rotated) — the real self-sovereign commit-path entry the node
//!     drives under `recursion`: the Effect-VM leg proves through the rotated IR-v2
//!     multi-table descriptor (`"effect-vm-rotated"`) + the PI-binding main proof, over a
//!     `FullTurnWitness` carrying a real `RotationTurnWitness`. The full real turn number.
//!   * `prove_vm_descriptor2` — the EPOCH IR-v2 multi-table batch STARK over the graduated
//!     transfer descriptor (the rotated leg's circuit, in isolation). The EffectVM sub-proof
//!     number under the live tower.
//!
//! (The v1 `prove_turn_self_sovereign` / hand-AIR `prove_effect_vm_p3` are RETIRED under
//! the recursion default — `prove_turn_self_sovereign` panics "thread a rotation witness".)
//!
//! SMOKE (default): the single rotated transfer. FULL (`PERF_FULL=1`): the rotated ladder.
//!
//! Run: `cargo bench -p dregg-perf --bench prove`
//! Persvati capture: `PERF_FULL=1 cargo bench -p dregg-perf --bench prove`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_perf::{cohort_transfer, prove_cohort, regime, rotated_turns};
use dregg_sdk::full_turn_proof::prove_full_turn;

/// The full LIVE rotated turn prover — the real commit path the node drives.
fn bench_prove_full_turn(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("prove_full_turn/{}", regime()));
    // Proving is seconds-scale; keep the sample count modest.
    group.sample_size(10);
    for (name, rt) in rotated_turns() {
        group.bench_function(name, |b| {
            b.iter(|| {
                let proof = prove_full_turn(black_box(&rt.witness)).expect("honest turn must prove");
                black_box(proof);
            });
        });
    }
    group.finish();
}

/// The EPOCH IR-v2 multi-table batch STARK for the graduated transfer descriptor (the
/// rotated leg's circuit in isolation) — the EffectVM sub-proof number.
fn bench_prove_descriptor(c: &mut Criterion) {
    let cohort = cohort_transfer();
    let mut group = c.benchmark_group(format!("prove_descriptor/{}", regime()));
    group.sample_size(10);
    group.bench_function("transfer_5table", |b| {
        b.iter(|| {
            let proof = prove_cohort(black_box(&cohort));
            black_box(proof);
        });
    });
    group.finish();
}

criterion_group!(benches, bench_prove_full_turn, bench_prove_descriptor);
criterion_main!(benches);
