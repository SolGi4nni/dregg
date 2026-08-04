//! # The sound-Pasta-multiply ATOM, priced at scale — the row-2 re-pricing, MEASURED.
//!
//! The in-AIR Kimchi/Wrap verifier plan prices "everything except the SRS bases" at **1.51 M rows /
//! 0.93 GB trace / 8–12 min prove**. Every one of those numbers is denominated in the sound Pasta
//! multiply (`PastaFieldSound.soundMulAir`, `dregg-pasta-fpmul-sound::v1`): 253 constraints, 190
//! DECLARED main columns, one row. This file measures what that atom actually costs the deployed
//! prover as the row count grows, so the plan's arithmetic rests on a measurement instead of a
//! model.
//!
//! ⚑ **THE COLUMN COUNT IN THE PLAN IS THE DECLARED ONE, AND THE PROVER DOES NOT COMMIT TO THAT.**
//! `MainLayout::build` appends a nibble-decomposition aux block per declared range lookup
//! (`LIMB_BITS = 4`), so the committed width is `trace_width + Σ decomp_cols(bits)`. This test
//! reports both, from the deployed `decomp_cols_pub`, rather than asserting either.
//!
//! ⚑ **THE PROBE ROW WHOSE TRUE COST IS ALREADY KNOWN** is `N = 8`: `3dcefe00a` measured it at
//! 173.8 ms prove / 18.8 ms verify in release. If this harness reports something far from that at
//! `N = 8`, the harness is broken and every other row here is noise. It is the first row printed
//! and it is asserted, not merely displayed.
//!
//! Run: `cargo nextest run -p dregg-circuit --release -E 'test(/sound_mul_scaling/)' --no-capture`
//! Cap the top row with `DREGG_SCALE_MAX_LOG_ROWS` (default 13, i.e. 8192 rows).

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};

const SOUND_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fpmul-sound.json");
const SOUND_TRACE: &str = include_str!("fixtures/pasta-fpmul-sound-trace.txt");
const SOUND_WIDTH: usize = 190;

fn sound_descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(SOUND_DESC_JSON).expect("the deployed checker parses the sound descriptor")
}

fn honest_rows() -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = SOUND_TRACE
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(rows.len(), 8, "the Lean-emitted honest fixture is 8 rows");
    assert!(rows.iter().all(|r| r.len() == SOUND_WIDTH));
    rows
}

/// `n` rows of honest multiply, by cycling the Lean-emitted honest block. The AIR is ROW-LOCAL
/// (63 coefficient gates + 190 range lookups, no `on_transition` leg), so every row of this trace
/// satisfies the same relation the 8-row fixture does — replication is a valid witness, not a
/// padding trick.
fn honest_n(n: usize) -> Vec<Vec<BabyBear>> {
    let base = honest_rows();
    (0..n).map(|i| base[i % base.len()].clone()).collect()
}

/// The committed main width: declared columns plus the nibble aux block each range lookup adds.
/// Read off the descriptor's own tables, through the deployed `decomp_cols_pub`.
fn committed_width(desc: &EffectVmDescriptor2) -> (usize, usize, usize) {
    let mut aux = 0usize;
    let mut nlk = 0usize;
    for c in &desc.constraints {
        if let VmConstraint2::Lookup(l) = c {
            if let Some(bits) =
                desc.tables
                    .iter()
                    .find(|t| t.id == l.table)
                    .and_then(|t| match t.sem {
                        TableSem::Range { bits } => Some(bits),
                        _ => None,
                    })
            {
                aux += decomp_cols_pub(bits);
                nlk += 1;
            }
        }
    }
    (desc.trace_width, desc.trace_width + aux, nlk)
}

#[test]
fn the_sound_multiply_scales_and_the_known_probe_row_holds() {
    let desc = sound_descriptor();
    let (declared, committed, nlk) = committed_width(&desc);

    println!("\n─── SOUND PASTA MULTIPLY — the atom, at scale ───");
    println!(
        "descriptor          {name}\nconstraints         {ncon}\n\
         declared columns    {declared}\ncommitted columns   {committed}  \
         (declared + nibble aux from {nlk} range lookups)\nwidth inflation     {infl:.2}x",
        name = desc.name,
        ncon = desc.constraints.len(),
        nlk = nlk,
        infl = committed as f64 / declared as f64,
    );
    println!(
        "\n{:>10}  {:>12}  {:>12}  {:>11}  {:>11}  {:>10}",
        "rows", "trace MiB", "LDE MiB@6", "prove ms", "verify ms", "proof KiB"
    );

    let max_log: u32 = std::env::var("DREGG_SCALE_MAX_LOG_ROWS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(13);

    let mut probe_ms = f64::NAN;
    for log_n in 3..=max_log {
        let n = 1usize << log_n;
        let trace = honest_n(n);
        let trace_mib = (n * committed * 4) as f64 / (1024.0 * 1024.0);
        let lde_mib = trace_mib * 64.0; // IR2_FRI_LOG_BLOWUP = 6

        let t0 = std::time::Instant::now();
        let proof = prove_vm_descriptor2(&desc, &trace, &[], &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("honest {n}-row trace must prove: {e}"));
        let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;

        let t1 = std::time::Instant::now();
        verify_vm_descriptor2(&desc, &proof, &[]).expect("and verifies");
        let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;

        let proof_kib = postcard::to_allocvec(&proof)
            .expect("serialize proof")
            .len() as f64
            / 1024.0;

        if log_n == 3 {
            probe_ms = prove_ms;
        }
        println!(
            "{n:>10}  {trace_mib:>12.2}  {lde_mib:>12.1}  {prove_ms:>11.1}  {verify_ms:>11.1}  \
             {proof_kib:>10.1}"
        );
    }

    // ⚑ THE PROBE. `3dcefe00a` measured the 8-row honest fixture at 173.8 ms prove in release.
    // A harness that has silently stopped proving (or is running in debug) cannot pass this.
    assert!(
        probe_ms > 20.0 && probe_ms < 3000.0,
        "the 8-row probe row measured {probe_ms:.1} ms; the recorded release cost is 173.8 ms. \
         Far outside that band means the harness is measuring something else (debug mode, a \
         cached proof, a different descriptor) and no row in this table is a measurement."
    );
}
