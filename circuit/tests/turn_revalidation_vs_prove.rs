//! REVALIDATION-vs-PROVE micro-bench — grounds the "commit on fast direct
//! validation, prove async" architecture fix (task #109: move proving OFF the
//! request path).
//!
//! THE QUESTION: over the SAME honest EffectVM turn (a transfer), how much
//! faster is DIRECT WITNESS REVALIDATION (an FRI-free constraint accept /
//! re-execution) than FULL STARK PROVING?
//!
//! The node's commit path currently proves every finalized turn through
//! `effect_vm_p3_full_air::prove_effect_vm_p3` (the audited `p3-batch-stark`
//! prover) BEFORE committing. If direct revalidation (constraint-check WITHOUT
//! FRI / proof generation) is microseconds-to-low-milliseconds while proving is
//! hundreds-of-ms-to-seconds, the commit path can revalidate cheaply inline and
//! move proving async.
//!
//! Five timed pathways over the identical (trace, PIs) the prover consumes:
//!
//!   1. PROVE      — `prove_effect_vm_p3(&trace, &pis)` (full STARK, self-verifies).
//!   2. VERIFY     — `verify_effect_vm_p3(&proof, &pis)` (audited verifier, no witness).
//!   3. P3-ACCEPT  — `p3_air_accepts(&trace, &pis)` (the RUNNING p3 AIR's
//!                   constraints checked by Plonky3's canonical FRI-free
//!                   `check_all_constraints` — exactly the predicate the audited
//!                   verifier enforces, deterministic, no FRI queries).
//!   4. DESC-ACCEPT— `descriptor_air_accepts(&desc, &trace, dpis)` (the
//!                   Lean-emitted descriptor interpreter's FRI-free accept — the
//!                   "ONE circuit" cutover path).
//!   5. REEXEC     — `generate_effect_vm_trace(&st, &effects)` (RE-EXECUTE the
//!                   turn to recompute the witness from scratch — the work the
//!                   commit path does to revalidate a submitted witness; a proxy
//!                   for the verified-executor re-apply, which needs a full
//!                   Turn+Ledger and is reported separately as a note).
//!
//! Run on persvati for clean numbers (it is a `#[test]` so it lives in the
//! tests/ target and needs no Cargo.toml stanza; `--nocapture` shows the table):
//!   scripts/pbuild perfbench cargo test -p dregg-circuit --release \
//!     --test turn_revalidation_vs_prove -- --nocapture --ignored
//!
//! It is `#[ignore]`d so a normal `cargo test` run does not pay the proving cost;
//! pass `--ignored` to run it. Harness is std::time::Instant (a hand-rolled
//! median over warmed iterations gives a sharp single-number table here).

use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace};
use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
use dregg_circuit::effect_vm_p3_full_air::{
    p3_air_accepts, prove_effect_vm_p3, verify_effect_vm_p3,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{descriptor_air_accepts, parse_vm_descriptor};

/// Median of a closure timed `iters` times (after `warmup` untimed runs).
/// Returns (median_secs, min_secs, n).
fn bench<F: FnMut()>(warmup: usize, iters: usize, mut f: F) -> (f64, f64, usize) {
    for _ in 0..warmup {
        f();
    }
    let mut samples: Vec<f64> = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t0 = Instant::now();
        f();
        samples.push(t0.elapsed().as_secs_f64());
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let median = samples[samples.len() / 2];
    let min = samples[0];
    (median, min, iters)
}

fn fmt_ms(secs: f64) -> String {
    let ms = secs * 1e3;
    if ms >= 1.0 {
        format!("{ms:>12.3} ms")
    } else {
        format!("{:>12.3} µs", secs * 1e6)
    }
}

#[test]
#[ignore = "perf micro-bench: runs the full STARK prover; run explicitly with --ignored --nocapture"]
fn turn_revalidation_vs_prove() {
    // --- THE turn: a single honest transfer (the verifiable-execution beachhead). ---
    let st = CellState::new(100_000, 0);
    let effects = vec![Effect::Transfer {
        amount: 50,
        direction: 1,
    }];

    // Witness the prover/verifier/accept-checks all consume.
    let (trace, pis) = generate_effect_vm_trace(&st, &effects);
    let trace_height = trace.len();
    let trace_width = trace.first().map(|r| r.len()).unwrap_or(0);

    // Descriptor side (the Lean-emitted "ONE circuit" cutover path) for selector 1 (TRANSFER).
    let desc_json = descriptor_for_selector(1).expect("transfer selector must have a descriptor");
    let desc = parse_vm_descriptor(desc_json).expect("transfer descriptor parses");
    let dpis: Vec<BabyBear> = pis[..desc.public_input_count].to_vec();

    // Sanity: the honest witness is accepted both ways, and proves+verifies, BEFORE we time.
    assert!(
        p3_air_accepts(&trace, &pis),
        "honest transfer must be p3-accepted"
    );
    assert!(
        descriptor_air_accepts(&desc, &trace, &dpis),
        "honest transfer must be descriptor-accepted"
    );
    let proof0 = prove_effect_vm_p3(&trace, &pis).expect("honest transfer proves");
    verify_effect_vm_p3(&proof0, &pis).expect("honest transfer verifies");

    eprintln!(
        "== EffectVM turn: single transfer | base trace {trace_height} rows x {trace_width} cols \
         | PIs {} (desc binds {}) ==",
        pis.len(),
        desc.public_input_count
    );

    // Proving dominates wall-clock; give it few iters, the cheap checks many.
    let (prove_med, prove_min, prove_n) = bench(2, 20, || {
        let p = prove_effect_vm_p3(&trace, &pis).expect("prove");
        std::hint::black_box(&p);
    });

    let (verify_med, verify_min, verify_n) = bench(5, 50, || {
        verify_effect_vm_p3(&proof0, &pis).expect("verify");
    });

    let (p3acc_med, p3acc_min, p3acc_n) = bench(10, 500, || {
        let ok = p3_air_accepts(&trace, &pis);
        std::hint::black_box(ok);
    });

    let (descacc_med, descacc_min, descacc_n) = bench(10, 500, || {
        let ok = descriptor_air_accepts(&desc, &trace, &dpis);
        std::hint::black_box(ok);
    });

    let (reexec_med, reexec_min, reexec_n) = bench(10, 500, || {
        let (t, p) = generate_effect_vm_trace(&st, &effects);
        std::hint::black_box((&t, &p));
    });

    // --- Report ---
    println!();
    println!("=================================================================================");
    println!("  REVALIDATION vs FULL STARK PROVING — same honest EffectVM transfer turn");
    println!("  (release build, persvati core; std::time::Instant median of warmed iters)");
    println!("=================================================================================");
    println!(
        "  {:<34} {:>16} {:>16} {:>6}",
        "pathway", "median", "min", "n"
    );
    println!("  ---------------------------------------------------------------------------");
    println!(
        "  {:<34} {:>16} {:>16} {:>6}",
        "1. PROVE  (full STARK)",
        fmt_ms(prove_med),
        fmt_ms(prove_min),
        prove_n
    );
    println!(
        "  {:<34} {:>16} {:>16} {:>6}",
        "2. VERIFY (audited verifier)",
        fmt_ms(verify_med),
        fmt_ms(verify_min),
        verify_n
    );
    println!(
        "  {:<34} {:>16} {:>16} {:>6}",
        "3. p3_air_accepts (FRI-free)",
        fmt_ms(p3acc_med),
        fmt_ms(p3acc_min),
        p3acc_n
    );
    println!(
        "  {:<34} {:>16} {:>16} {:>6}",
        "4. descriptor_air_accepts (FRI-free)",
        fmt_ms(descacc_med),
        fmt_ms(descacc_min),
        descacc_n
    );
    println!(
        "  {:<34} {:>16} {:>16} {:>6}",
        "5. re-exec (regenerate witness)",
        fmt_ms(reexec_med),
        fmt_ms(reexec_min),
        reexec_n
    );
    println!("  ---------------------------------------------------------------------------");

    let sp_p3 = prove_med / p3acc_med;
    let sp_desc = prove_med / descacc_med;
    let sp_reexec = prove_med / reexec_med;
    let sp_verify = prove_med / verify_med;
    println!("  SPEEDUP of direct revalidation vs full PROVE (median):");
    println!("    prove / p3_air_accepts          = {sp_p3:>10.1}x");
    println!("    prove / descriptor_air_accepts  = {sp_desc:>10.1}x");
    println!("    prove / re-exec (witness)       = {sp_reexec:>10.1}x");
    println!("    prove / verify                  = {sp_verify:>10.1}x  (for reference)");
    println!("=================================================================================");
    println!(
        "  NOTE: pathway 5 (re-exec) recomputes the FULL witness from the effect; it is a\n  \
         proxy for the verified-executor re-apply. The true executor re-apply needs a full\n  \
         Turn+Ledger (TurnExecutor::execute) — heavier setup, not timed here, but it does NO\n  \
         FRI/proving so it lives in the same milliseconds-or-less regime as 3/4/5, not 1."
    );
    println!();
}
