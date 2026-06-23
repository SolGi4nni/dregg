//! Criterion bench: SYMBOLIC vs FULL + COLLAPSE — THE HEADLINE INTERACTIVITY NUMBER.
//!
//! A batch of N real transfer turns through the EMBEDDED `World` (the gpui-free
//! `starbridge_v2::world::World`, the same verified executor the node and the seL4
//! `executor` PD drive), run two ways:
//!
//!   * `full_batch`     — `WitnessMode::Full`: every committed turn materializes its
//!     per-turn Merkle witness (`Ledger::root()` + the replay-tape double-execution).
//!     This is the publishable default — what a node pays to admit a turn that may
//!     immediately cross the publish boundary.
//!   * `symbolic_batch` — `WitnessMode::Symbolic`: the FULL state transition applies
//!     (every legality gate still fires — symbolic defers the WITNESS, never the
//!     DECISION), but `Ledger::root()` and the replay double-execution are SKIPPED.
//!     The turns are buffered for later collapse. This is the local interactive fast
//!     path (`turn/src/collapse.rs`).
//!   * `collapse_N`     — `World::collapse`: re-run the buffered symbolic batch under
//!     Full on the replay recorder to materialize the real witnesses ON DEMAND. The
//!     one-time cost paid only when the symbolic work is published.
//!
//! THE HEADLINE: `symbolic_batch` vs `full_batch` is the per-turn speedup symbolic
//! mode buys (the witness/commitment cost it removes from the interactive loop), and
//! `collapse_N` is the deferred witness cost — paid once, at publish, instead of per
//! turn. Co-located in one group so the speedup + the amortized collapse cost read
//! off directly against the SAME batch shape.
//!
//! SMOKE (default): N=8 turns. FULL (`PERF_FULL=1`): N ∈ {8, 64, 256} — the
//! interactive-session length ladder.
//!
//! Run: `cargo bench -p dregg-perf --bench symbolic_collapse`

use criterion::{BatchSize, Criterion, black_box, criterion_group, criterion_main};
use dregg_perf::regime;
use dregg_turn::collapse::WitnessMode;
use starbridge_v2::world::{World, demo_world, transfer};

/// The batch-size ladder: how many turns make up one interactive session.
fn batch_sizes() -> &'static [usize] {
    if dregg_perf::perf_full() {
        &[8, 64, 256]
    } else {
        &[8]
    }
}

/// Build a fresh demo world (three anchor cells + an issuer well, seeded through the
/// real genesis + five executor turns) and the treasury→user agent/target pair the
/// batch transfers between. The treasury starts with 1_000_000, so a batch of small
/// outgoing transfers stays conserving and within balance.
fn fresh_world() -> (World, dregg_cell::CellId, dregg_cell::CellId) {
    let (w, [treasury, _service, user]) = demo_world();
    (w, treasury, user)
}

/// Commit `n` single-transfer turns of `1` unit each from `treasury` to `user`
/// against `world` (in whatever witness mode the world is currently in). Returns
/// the number that committed (asserted == n in the bench).
fn run_batch(world: &mut World, treasury: dregg_cell::CellId, user: dregg_cell::CellId, n: usize) -> usize {
    let mut committed = 0;
    for _ in 0..n {
        let turn = world.turn(treasury, vec![transfer(treasury, user, 1)]);
        if world.commit_turn(turn).is_committed() {
            committed += 1;
        }
    }
    committed
}

fn bench_symbolic_collapse(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("symbolic_collapse/{}", regime()));
    // The Full batch dominates the wall-clock budget at large N; keep samples modest.
    group.sample_size(20);

    for &n in batch_sizes() {
        // ---- FULL: the publishable default (witness every turn) -------------
        group.bench_function(format!("full_batch_{n}"), |b| {
            b.iter_batched(
                fresh_world,
                |(mut world, treasury, user)| {
                    world.set_witness_mode(WitnessMode::Full);
                    let committed = run_batch(&mut world, treasury, user, n);
                    debug_assert_eq!(committed, n, "every honest full turn must commit");
                    black_box(committed);
                },
                BatchSize::SmallInput,
            );
        });

        // ---- SYMBOLIC: the local interactive fast path (defer the witness) ---
        group.bench_function(format!("symbolic_batch_{n}"), |b| {
            b.iter_batched(
                fresh_world,
                |(mut world, treasury, user)| {
                    world.set_witness_mode(WitnessMode::Symbolic);
                    let committed = run_batch(&mut world, treasury, user, n);
                    debug_assert_eq!(committed, n, "every honest symbolic turn must commit");
                    debug_assert_eq!(world.symbolic_pending(), n, "symbolic turns buffered");
                    black_box(committed);
                },
                BatchSize::SmallInput,
            );
        });

        // ---- COLLAPSE: materialize the deferred witnesses ON DEMAND ----------
        // Setup runs the symbolic batch (untimed); the timed body collapses it.
        group.bench_function(format!("collapse_{n}"), |b| {
            b.iter_batched(
                || {
                    let (mut world, treasury, user) = fresh_world();
                    world.set_witness_mode(WitnessMode::Symbolic);
                    let committed = run_batch(&mut world, treasury, user, n);
                    debug_assert_eq!(committed, n);
                    world
                },
                |mut world| {
                    let collapsed = world.collapse().expect("honest symbolic batch must collapse");
                    debug_assert_eq!(collapsed, n, "all buffered turns collapse");
                    black_box(collapsed);
                },
                BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

criterion_group!(benches, bench_symbolic_collapse);
criterion_main!(benches);
