//! Standalone turn-proof performance summary — prints a table of real
//! prove/verify wall-clock times for the LIVE rotated self-sovereign turn path
//! (`prove_full_turn` / `verify_full_turn` over a real `RotationTurnWitness`). Under
//! the `recursion` default the EffectVM leg proves through the rotated IR-v2 descriptor
//! tower (the v1 `prove_turn_self_sovereign` entry is retired and panics).
//!
//! Run: `cargo run --release -p dregg-perf --bin perf-summary`
//!
//! Unlike the criterion bench, this is a single-shot report meant to be pasted
//! into the product assessment. It warms once, then times a few iterations and
//! reports the mean, so the numbers are reproducible without the full criterion
//! harness.

use std::time::Instant;

use dregg_perf::rotated_turns;
use dregg_sdk::full_turn_proof::{prove_full_turn, verify_full_turn};

fn fmt(secs: f64) -> String {
    if secs < 1e-3 {
        format!("{:.1} us", secs * 1e6)
    } else if secs < 1.0 {
        format!("{:.1} ms", secs * 1e3)
    } else {
        format!("{:.3} s", secs)
    }
}

fn main() {
    println!(
        "{:<20} {:>12} {:>12}",
        "workload", "prove (mean)", "verify (mean)"
    );
    println!("{}", "-".repeat(46));

    for (name, rt) in rotated_turns() {
        // Warm + correctness gate.
        let proof = prove_full_turn(&rt.witness).expect("honest turn must prove");
        verify_full_turn(&proof, rt.old_commit, rt.new_commit).expect("honest proof must verify");

        let prove_iters = 5u32;
        let t0 = Instant::now();
        for _ in 0..prove_iters {
            let p = prove_full_turn(&rt.witness).expect("prove");
            std::hint::black_box(&p);
        }
        let prove_mean = t0.elapsed().as_secs_f64() / prove_iters as f64;

        let verify_iters = 50u32;
        let t1 = Instant::now();
        for _ in 0..verify_iters {
            verify_full_turn(&proof, rt.old_commit, rt.new_commit).expect("verify");
        }
        let verify_mean = t1.elapsed().as_secs_f64() / verify_iters as f64;

        println!(
            "{:<20} {:>12} {:>12}",
            name,
            fmt(prove_mean),
            fmt(verify_mean)
        );
    }
}
