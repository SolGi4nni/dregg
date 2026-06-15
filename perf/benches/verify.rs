//! Criterion bench: PROOF VERIFY.
//!
//! Times `verify_full_turn` — the self-sovereign turn verifier the light client
//! runs — on a pre-built honest ROTATED proof. Verify is the light side of the system
//! and the dominant cost a LIGHT CLIENT pays, so it is benchmarked separately from
//! prove. Under the `recursion` default the verified leg is the rotated IR-v2 descriptor
//! chain (the v1 `prove_turn_self_sovereign` path is retired).
//!
//! SMOKE (default): verify the single rotated transfer proof.
//! FULL (`PERF_FULL=1`): verify across the rotated-turn ladder.
//!
//! Run: `cargo bench -p dregg-perf --bench verify`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_perf::{regime, rotated_turns};
use dregg_sdk::full_turn_proof::{prove_full_turn, verify_full_turn};

fn bench_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("verify/{}", regime()));
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

criterion_group!(benches, bench_verify);
criterion_main!(benches);
