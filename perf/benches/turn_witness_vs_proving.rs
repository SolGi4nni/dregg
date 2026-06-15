//! Criterion bench: THE WITNESS-ONLY vs FULL-PROVING CONTRAST (the headline number).
//!
//! Times BOTH halves of one turn SIDE BY SIDE, in a single criterion group, so the
//! proving multiplier is read off directly:
//!
//!   * `witness_only` — the live Rust `TurnExecutor::execute` over a `Ledger`: state
//!     lookup, authorization gating, effect application, receipt + commitment. This is
//!     the path a node runs to ADMIT a turn when it is NOT minting a SNARK (the
//!     witness-only / unproven-commit hot path). Microseconds-scale.
//!   * `witness_gen` — `generate_effect_vm_trace`: the Effect-VM witness the prover
//!     consumes (built whether or not a proof is then minted). Sub-millisecond.
//!   * `full_proving` — `prove_turn_self_sovereign`: the real self-sovereign commit-path
//!     entry, EffectVM leg (rotated IR-v2 descriptor under the `recursion` default) +
//!     PI-binding main proof. Seconds-scale.
//!   * `verify` — `verify_full_turn`: the light side a verifier/light-client pays.
//!
//! The point of co-locating them: `full_proving / witness_only` is THE cost the
//! "prove every turn vs admit-then-prove-async" product decision turns on. Both run
//! over the SAME canonical single-Transfer turn so the ratio is apples-to-apples.
//!
//! SMOKE (default): the single smallest real turn. FULL (`PERF_FULL=1`): the
//! 1/4/16-effect ladder for the proving + verify legs.
//!
//! Run: `cargo bench -p dregg-perf --bench turn_witness_vs_proving`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_perf::{
    build_trace, executor_transfer_turn, fresh_executor, regime, rotated_turns, single_transfer,
};
use dregg_sdk::full_turn_proof::{prove_full_turn, verify_full_turn};

/// One group holding every leg of a turn's cost so the proving multiplier reads off
/// directly. The witness-only + witness-gen legs are over the canonical single-Transfer
/// (they are the same shape regardless of the proving ladder); the proving + verify legs
/// sweep the rotated-turn ladder under FULL. The full-proving leg is the LIVE rotated
/// `prove_full_turn` (the v1 `prove_turn_self_sovereign` is retired under recursion).
fn bench_contrast(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("turn_witness_vs_proving/{}", regime()));
    // Proving dominates the wall-clock budget; keep its sample count modest. The
    // microsecond legs still get criterion's full statistical treatment.
    group.sample_size(10);

    // ---- WITNESS-ONLY: the executor admit path (no SNARK) -------------------
    let executor = fresh_executor();
    group.bench_function("witness_only_executor_execute", |b| {
        b.iter_batched(
            executor_transfer_turn,
            |(mut ledger, turn)| {
                let result = executor.execute(black_box(&turn), black_box(&mut ledger));
                debug_assert!(result.is_committed(), "honest open-cell turn must commit");
                black_box(result);
            },
            criterion::BatchSize::SmallInput,
        );
    });

    // ---- WITNESS-GEN: the Effect-VM trace the prover consumes ---------------
    let (st, effs) = single_transfer();
    group.bench_function("witness_gen_effect_vm_trace", |b| {
        b.iter(|| {
            let (trace, pis) = build_trace(&dregg_perf::Workload {
                name: "transfer_1effect",
                initial: st.clone(),
                effects: effs.clone(),
            });
            black_box((trace, pis));
        });
    });

    // ---- FULL-PROVING: the LIVE rotated self-sovereign turn prover -----------
    for (name, rt) in rotated_turns() {
        group.bench_function(format!("full_proving_{name}"), |b| {
            b.iter(|| {
                let proof = prove_full_turn(black_box(&rt.witness)).expect("honest turn must prove");
                black_box(proof);
            });
        });
    }

    // ---- VERIFY: the light-client side --------------------------------------
    for (name, rt) in rotated_turns() {
        let proof = prove_full_turn(&rt.witness).expect("honest turn must prove");
        group.bench_function(format!("verify_{name}"), |b| {
            b.iter(|| {
                verify_full_turn(black_box(&proof), rt.old_commit, rt.new_commit)
                    .expect("honest proof must verify");
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_contrast);
criterion_main!(benches);
