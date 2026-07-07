//! Benchmark: the injection leg BEFORE (legacy hand STARK, `dregg_circuit::stark` via
//! `prove_dfa_routing`) vs AFTER (the plonky3 IR-v2 descriptor prover, `prove_injection_leg`).
//!
//! Run: `cargo run -p dregg-zkoracle-prove --release --example bench_injection_leg`
//!
//! The 1KB field → 1024 trace rows; the 8KB field → 8192 rows. The legacy engine is O(n²), so the
//! 8KB BEFORE is not run (it would take many minutes); the 1KB BEFORE is timed for a real anchor.

use std::time::Instant;

use dregg_circuit::dsl::dfa_routing::prove_dfa_routing;
use dregg_zkoracle_prove::zk_leg::{injection_dfa_table, prove_injection_leg, verify_injection_leg};

/// A benign (injection-free) field of exactly `n` bytes: a repeated sentence, no `{{`.
fn benign_field(n: usize) -> Vec<u8> {
    let seed = b"The capital of France is Paris. ";
    let mut v = Vec::with_capacity(n);
    while v.len() < n {
        v.push(seed[v.len() % seed.len()]);
    }
    v.truncate(n);
    v
}

/// Symbols the legacy `prove_dfa_routing` consumes (1 = `{`, 0 = other).
fn symbols_of(field: &[u8]) -> Vec<u32> {
    field
        .iter()
        .map(|&b| if b == b'{' { 1 } else { 0 })
        .collect()
}

fn main() {
    println!("== injection-leg prover benchmark (BEFORE hand-STARK vs AFTER descriptor prover) ==\n");

    for &kb in &[1usize, 8usize] {
        let n = kb * 1024;
        let field = benign_field(n);
        let rows = n.next_power_of_two().max(2);
        println!("--- {kb}KB field ({n} bytes → {rows} trace rows) ---");

        // AFTER: the descriptor prover.
        let t = Instant::now();
        let leg = prove_injection_leg(&field).expect("prove (descriptor)");
        let after = t.elapsed();
        verify_injection_leg(&field, &leg).expect("verify (descriptor)");
        let proof_kb = leg.proof_bytes.len() as f64 / 1024.0;
        println!("  AFTER  (descriptor prover): {after:?}  [proof {proof_kb:.1} KiB, verified OK]");

        // BEFORE: the legacy hand STARK (O(n²)). Only run at 1KB; 8KB would take minutes.
        if kb <= 1 {
            let table = injection_dfa_table();
            let syms = symbols_of(&field);
            let t = Instant::now();
            let (_proof, _pi) = prove_dfa_routing("zkoracle-injection-v1", &table, 0, &syms)
                .expect("prove (legacy hand STARK)");
            let before = t.elapsed();
            println!("  BEFORE (legacy hand STARK): {before:?}");
            println!(
                "  SPEEDUP: {:.1}×",
                before.as_secs_f64() / after.as_secs_f64()
            );
        } else {
            println!("  BEFORE (legacy hand STARK): not run (O(n²); ~minutes at this size)");
        }
        println!();
    }
}
