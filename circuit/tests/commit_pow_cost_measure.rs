//! **Pricing `commit_proof_of_work_bits` — the knob no ledger column priced.**
//!
//! plonky3 carries TWO grinding knobs (`fri/src/config.rs`): `query_proof_of_work_bits`, ground
//! once before the query indices are sampled, and `commit_proof_of_work_bits`, ground **per fold
//! round, after the round commitment is observed and before the folding challenge `β` is drawn**
//! (`fri/src/prover.rs:224`; checked by `fri/src/verifier.rs:222`, which also pins the witness
//! count to the commit count at `:206`). Every dregg config sets the second to `0`.
//!
//! The commit knob grinds against exactly the phase BCIKS20's `ε_C` term bounds, and `ε_C` is the
//! branch that BINDS at the deployed pairing (`FriDeployedHeightPairing.the_commit_column_binds_at_
//! the_deployed_pairing`: `min{51, 73}`). So its price is the price of the only lever on the
//! binding branch that is not a field-extension flag day.
//!
//! **What this measures, and what it does not.** This is a COST measurement: permutations per
//! second, and therefore seconds of prover wall-clock per `(rounds, bits)` pair. It says nothing
//! about how many bits the grinding buys — that is
//! `Dregg2.Circuit.FriCommitPow.commitPowBranch`, in Lean, where the column belongs. ⚑ It also does
//! not decide whether a setting is REACHABLE: `grind` asserts `(1u64 << bits) < F::ORDER_U64` over a
//! single base-field witness, so BabyBear caps both PoW knobs at 30 bits
//! (`FriCommitPow.maxGrindBits_is_the_babybear_witness_cap`), and the table below says so per row.
//!
//! Run:
//!   cargo test -p dregg-circuit --release --test commit_pow_cost_measure -- --ignored --nocapture

use std::time::Instant;

use p3_baby_bear::{BabyBear, default_babybear_poseidon2_16};
use p3_challenger::{DuplexChallenger, GrindingChallenger};

type Perm16 = p3_baby_bear::Poseidon2BabyBear<16>;
type Ch = DuplexChallenger<BabyBear, Perm16, 16, 8>;

fn challenger() -> Ch {
    DuplexChallenger::new(default_babybear_poseidon2_16())
}

/// The deployed fold-round count: `⌈(logD0 − logBlowup) / maxLogArity⌉` at the wrap pairing
/// `|D⁽⁰⁾| = 2^22` (`WRAP_LOG_CEIL 16` × `IR2_INNER_LOG_BLOWUP 6`), `maxLogArity = 1`.
const DEPLOYED_FOLD_ROUNDS: u32 = 16;

/// Measure the grind rate by timing a real `grind` at `bits` and dividing by its expected work.
/// `grind` searches for a witness whose absorbed state samples `bits` zero bits, so the expected
/// number of permutations is `2^bits`. Timing a single grind at a moderate `bits` is a direct,
/// unbiased estimate of permutations/second on this machine.
fn grind_rate_per_sec(bits: usize, reps: usize) -> f64 {
    let mut best = f64::INFINITY;
    for _ in 0..reps {
        let mut ch = challenger();
        let t0 = Instant::now();
        let w = ch.grind(bits);
        let dt = t0.elapsed().as_secs_f64();
        // keep the witness observably used so nothing is optimised away
        assert!(w != BabyBear::new(u32::MAX));
        if dt < best {
            best = dt;
        }
    }
    (1u64 << bits) as f64 / best
}

#[test]
#[ignore = "MEASUREMENT: grinds ~2^22 Poseidon2 permutations. Run with --ignored --nocapture."]
fn commit_pow_price_per_bit() {
    // Calibrate on several widths so the rate is not an artefact of one sample.
    let mut rates = Vec::new();
    for bits in [16usize, 18, 20, 22] {
        let r = grind_rate_per_sec(bits, 3);
        println!("  calibration grind({bits:>2}) -> {:>12.0} perms/s", r);
        rates.push(r);
    }
    // Use the SLOWEST observed rate: over-estimating cost is the conservative direction for a
    // knob we are about to recommend turning on. (A single `grind` has a geometric trial count, so
    // the spread across these samples is the distribution, not measurement error.)
    let rate = rates.iter().cloned().fold(f64::INFINITY, f64::min);
    println!("\n  conservative ACHIEVED rate: {rate:.0} Poseidon2-BabyBear witness trials/s\n");

    // ⚑ CORRECTED 2026-08-14 — THE PREMISE OF THIS PARAGRAPH LEFT THE TREE FIVE DAYS AFTER IT WAS
    // WRITTEN, AND THE PARAGRAPH DID NOT.
    //
    // It used to read: "`grind` is ALREADY both SIMD-packed and rayon-parallel
    // (`into_par_iter().find_map_any`) … the rate above is therefore a WHOLE-MACHINE rate, not a
    // per-core one: there is no further thread multiplier to apply, and a column that applied one
    // would be counting the same parallelism twice."
    //
    // `90680ee7d` (2026-08-02) replaced `find_map_any` with **`find_map_first`** so the PoW witness
    // would stop depending on thread scheduling — correct, and every byte-parity gate needs it. But
    // `find_first` must prove no LOWER candidate exists, and the witness sits in the first ~0.003%
    // of the range, so rayon's thief-driven splitter leaves the worker that owns index 0 walking to
    // the answer alone.
    //
    // MEASURED (`tests/grind_phase_measure.rs` §G3, contention-free instrument = max batches
    // scanned by any ONE worker): the critical path is **20,766 batches at 1 thread and 20,766 at
    // 12 — scale 1.00, flat** — while TOTAL work rises from 20,766 to 123,517 and wall clock gets
    // WORSE (24.4 ms → 28.9 ms). So:
    //
    //   * The rate above is the ACHIEVED rate, and it is a SINGLE-CORE rate wearing a whole-machine
    //     name. The seconds column below is therefore still CORRECT AS MEASURED — do not multiply
    //     it by anything — but it is not a hardware floor.
    //   * A windowed parallel-`min` grind (§G3 strategy C) returns BYTE-FOR-BYTE the same witness
    //     and measures **7.49× on the critical path at 12 threads**. If that lands, every seconds
    //     figure below divides by ~T, and `commit_proof_of_work_bits` gets ~3.6 bits cheaper.
    //
    // The old sentence was written to stop a reader double-counting parallelism; today it makes one
    // count parallelism that is gone. Leaving it would be keeping a cost verdict whose premise is
    // refuted, which is worse than having no comment at all.
    println!(
        "  {:<10}{:>16}{:>20}{:>14}",
        "cpow bits", "perms total", "achieved (s)", "runnable?"
    );
    println!("  {}", "-".repeat(62));
    for cpow in [0usize, 8, 12, 16, 20, 24, 26, 28, 30, 31, 32] {
        let perms = DEPLOYED_FOLD_ROUNDS as f64 * (2f64).powi(cpow as i32);
        // plonky3 asserts `(1u64 << bits) < F::ORDER_U64` and grinds a SINGLE base-field witness,
        // so BabyBear caps BOTH pow knobs at 30 bits. Above it the prover asserts out.
        let runnable = if (1u64 << cpow) < 2013265921 {
            "yes"
        } else {
            "ASSERTS OUT"
        };
        println!(
            "  {:<10}{:>16.3e}{:>20.2}{:>14}",
            cpow,
            perms,
            perms / rate,
            runnable
        );
    }
    println!(
        "\n  (grinding is VERIFIER-FREE: the verifier does one `check_witness` per fold round —\n   \
         {DEPLOYED_FOLD_ROUNDS} extra permutations total — and the proof grows by one BabyBear field\n   \
         element per fold round, i.e. {} bytes. It is also EMBARRASSINGLY PARALLELISABLE, which is\n   \
         not the same as parallel: measured, the deployed `find_map_first` search scales 1.00× from\n   \
         1 to 12 threads — see `grind_phase_measure.rs` §G3 and the corrected note above.)",
        DEPLOYED_FOLD_ROUNDS * 4
    );
}
