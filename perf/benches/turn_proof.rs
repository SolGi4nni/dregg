//! Criterion bench for the PRODUCTION turn-proof path.
//!
//! Times the LIVE rotated full-turn prover + verifier — `prove_full_turn` /
//! `verify_full_turn` over a `FullTurnWitness` carrying a real `RotationTurnWitness`
//! (minted by `dregg_turn::rotation_witness::produce`), the path the node drives under
//! the `recursion` default (the Effect-VM leg proves through the rotated IR-v2 descriptor
//! tower; the v1 `prove_turn_self_sovereign` fallback is RETIRED and panics). This is the
//! "how long does a real turn take to prove?" number the product assessment needs, measured.
//!
//! Run: `cargo bench -p dregg-perf --bench turn_proof`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_perf::{regime, rotated_turns};
use dregg_sdk::full_turn_proof::{prove_full_turn, verify_full_turn};

fn bench_prove(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("turn_prove/{}", regime()));
    // Proving is seconds-scale; keep the sample count modest so the wall-clock
    // budget stays reasonable.
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

fn bench_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("turn_verify/{}", regime()));
    for (name, rt) in rotated_turns() {
        let proof = prove_full_turn(&rt.witness).expect("honest turn must prove");
        group.bench_function(name, |b| {
            b.iter(|| {
                verify_full_turn(black_box(&proof), rt.old_commit, rt.new_commit)
                    .expect("honest proof must verify");
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_prove, bench_verify);
criterion_main!(benches);
