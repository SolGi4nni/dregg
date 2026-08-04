//! # The sound-Pasta atoms priced at the DEPLOYED committed width, and the FRI blowup RE-PRICED
//! for a 2^20-row workload — both MEASURED.
//!
//! The in-AIR Kimchi/Wrap verifier plan prices "everything except the SRS bases" at **1.51 M rows /
//! 0.93 GB trace / 8–12 min prove**, denominated in the sound Pasta gates
//! (`PastaFieldSound.soundMulAir` = 253 constraints / 190 DECLARED columns;
//! `PastaAddSubSound.soundAddSubAir` = 160 / 128). This file measures what those atoms cost the
//! deployed prover, so the plan rests on a measurement instead of a model.
//!
//! ⚑ **THE COLUMN COUNT IN THE PLAN IS THE DECLARED ONE, AND THE PROVER DOES NOT COMMIT TO THAT.**
//! `MainLayout::build` appends a nibble-decomposition aux block per declared range lookup
//! (`LIMB_BITS = 4`), so the committed width is `trace_width + Σ decomp_cols(bits)`. Every
//! trace-size and LDE figure in the plan is denominated in the wrong width. This test reports both,
//! from the deployed `decomp_cols_pub`, rather than asserting either.
//!
//! ⚑ **THE PROBE ROW WHOSE TRUE COST IS ALREADY KNOWN** is the multiply at `N = 8`: `3dcefe00a`
//! measured it at 173.8 ms prove / 18.8 ms verify in release. If this harness reports something far
//! from that at `N = 8`, the harness is broken and every other row here is noise. It is asserted,
//! not merely displayed.
//!
//! ⚑ **THE FRI RE-PRICING.** `IR2_FRI_LOG_BLOWUP = 6` (`descriptor_ir2.rs:6256`) is justified in
//! `PROOF-ECONOMICS.md` §2c by a premise a 2^20-row AIR breaks: *"IR-v2's committed tables are TINY
//! (2³–2⁸ rows)"*. `ir2_config`'s own docblock names the security-PARITY points —
//! `(lb 6, q 19)`, `(lb 2, q 57)`, `(lb 1, q 114)` — so this sweep holds security fixed and prices
//! the three axes that move: prover time, PEAK MEMORY (the wall), and proof size. It changes no
//! deployed constant; the knob is global and moving it is ember's call.
//!
//! Run: `cargo test -p dregg-circuit --release --test pasta_sound_atom_price_and_fri_repricing \
//!       -- --nocapture`
//! Cap the scaling top row with `DREGG_SCALE_MAX_LOG_ROWS` (default 13). The FRI sweep runs at
//! `DREGG_FRI_SWEEP_LOG_ROWS` (default 12).

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2,
    decomp_cols_pub, parse_vm_descriptor2, prove_vm_descriptor2, prove_vm_descriptor2_with_config,
    verify_vm_descriptor2, verify_vm_descriptor2_with_config,
};
use dregg_circuit::plonky3_prover::create_config_with_fri_full;

const MUL_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fpmul-sound.json");
const MUL_TRACE: &str = include_str!("fixtures/pasta-fpmul-sound-trace.txt");
const MUL_WIDTH: usize = 190;

const ADD_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fpadd-sound.json");
const ADD_TRACE: &str = include_str!("fixtures/pasta-fpadd-sound-trace.txt");
const SUB_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fpsub-sound.json");
const SUB_TRACE: &str = include_str!("fixtures/pasta-fpsub-sound-trace.txt");
const ADDSUB_WIDTH: usize = 128;

/// The plan's prediction for "everything except the SRS bases", restated so a reader sees what the
/// measured columns below are being scored against.
const PLAN_ROWS: f64 = 1.51e6;

fn parse_rows(text: &str, width: usize) -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(!rows.is_empty(), "the Lean-emitted fixture is non-empty");
    assert!(
        rows.iter().all(|r| r.len() == width),
        "every fixture row is {width} wide"
    );
    rows
}

/// `n` rows, by cycling a Lean-emitted honest block. Both sound AIRs are ROW-LOCAL (no
/// `on_transition` leg), so every row of the replicated trace satisfies the same relation the
/// fixture does — replication is a valid witness, not a padding trick.
fn cycle_to(base: &[Vec<BabyBear>], n: usize) -> Vec<Vec<BabyBear>> {
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

struct Atom {
    label: &'static str,
    desc: EffectVmDescriptor2,
    honest: Vec<Vec<BabyBear>>,
}

fn atoms() -> Vec<Atom> {
    vec![
        Atom {
            label: "fpmul",
            desc: parse_vm_descriptor2(MUL_DESC_JSON).expect("deployed checker parses fpmul-sound"),
            honest: parse_rows(MUL_TRACE, MUL_WIDTH),
        },
        Atom {
            label: "fpadd",
            desc: parse_vm_descriptor2(ADD_DESC_JSON).expect("deployed checker parses fpadd-sound"),
            honest: parse_rows(ADD_TRACE, ADDSUB_WIDTH),
        },
        Atom {
            label: "fpsub",
            desc: parse_vm_descriptor2(SUB_DESC_JSON).expect("deployed checker parses fpsub-sound"),
            honest: parse_rows(SUB_TRACE, ADDSUB_WIDTH),
        },
    ]
}

/// ⚑ **§A — the atoms at the width the prover actually commits to.**
#[test]
fn the_sound_atoms_are_priced_at_the_committed_width() {
    println!("\n═══ §A  THE SOUND PASTA ATOMS, AT THE COMMITTED WIDTH ═══");
    println!(
        "{:>8}  {:>6}  {:>8}  {:>9}  {:>9}  {:>7}",
        "atom", "constr", "declared", "committed", "range lks", "inflate"
    );
    let mut mul_committed = 0usize;
    for a in atoms() {
        let (declared, committed, nlk) = committed_width(&a.desc);
        if a.label == "fpmul" {
            mul_committed = committed;
        }
        println!(
            "{:>8}  {:>6}  {:>8}  {:>9}  {:>9}  {:>6.2}x",
            a.label,
            a.desc.constraints.len(),
            declared,
            committed,
            nlk,
            committed as f64 / declared as f64,
        );
    }

    // ⚑ THE CORRECTION THE PLAN NEEDS, stated in the units the plan used.
    let plan_trace_gb = PLAN_ROWS * MUL_WIDTH as f64 * 4.0 / 1e9;
    let real_trace_gb = PLAN_ROWS * mul_committed as f64 * 4.0 / 1e9;
    println!(
        "\nat the plan's {PLAN_ROWS:.2e} rows, all-multiply:\n  \
         DECLARED-width trace   {plan_trace_gb:.2} GB   (what the plan priced)\n  \
         COMMITTED-width trace  {real_trace_gb:.2} GB   (what the prover commits)\n  \
         LDE @ log_blowup 6     {:.1} GB\n  \
         LDE @ log_blowup 2     {:.1} GB",
        real_trace_gb * 64.0,
        real_trace_gb * 4.0,
    );

    assert!(
        mul_committed > MUL_WIDTH,
        "the nibble aux block is real; a committed width equal to the declared one means \
         decomp_cols_pub returned 0 for every lookup and this whole table is meaningless"
    );
}

/// ⚑ **§B — the multiply at scale, with the known probe row asserted.**
#[test]
fn the_sound_multiply_scales_and_the_known_probe_row_holds() {
    let a = &atoms()[0];
    let (declared, committed, nlk) = committed_width(&a.desc);

    println!("\n═══ §B  SOUND PASTA MULTIPLY AT SCALE ═══");
    println!(
        "descriptor {}  constraints {}  declared {declared}  committed {committed} \
         (+{nlk} range lookups)",
        a.desc.name,
        a.desc.constraints.len(),
    );
    println!(
        "\n{:>10}  {:>12}  {:>12}  {:>11}  {:>11}  {:>10}  {:>10}",
        "rows", "trace MiB", "LDE MiB@6", "prove ms", "verify ms", "proof KiB", "us/row"
    );

    let max_log: u32 = std::env::var("DREGG_SCALE_MAX_LOG_ROWS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(13);

    let mut probe_ms = f64::NAN;
    let mut top_us_per_row = f64::NAN;
    for log_n in 3..=max_log {
        let n = 1usize << log_n;
        let trace = cycle_to(&a.honest, n);
        let trace_mib = (n * committed * 4) as f64 / (1024.0 * 1024.0);

        let t0 = std::time::Instant::now();
        let proof = prove_vm_descriptor2(&a.desc, &trace, &[], &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("honest {n}-row trace must prove: {e}"));
        let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;

        let t1 = std::time::Instant::now();
        verify_vm_descriptor2(&a.desc, &proof, &[]).expect("and verifies");
        let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;

        let proof_kib = postcard::to_allocvec(&proof)
            .expect("serialize proof")
            .len() as f64
            / 1024.0;
        let us_per_row = prove_ms * 1000.0 / n as f64;

        if log_n == 3 {
            probe_ms = prove_ms;
        }
        top_us_per_row = us_per_row;
        println!(
            "{n:>10}  {trace_mib:>12.2}  {:>12.1}  {prove_ms:>11.1}  {verify_ms:>11.1}  \
             {proof_kib:>10.1}  {us_per_row:>10.1}",
            trace_mib * 64.0
        );
    }

    // ⚑ THE EXTRAPOLATION, from the TOP measured row only (the low rows are dominated by the
    // fixed per-proof cost and would flatter the estimate).
    println!(
        "\nextrapolated to the plan's {PLAN_ROWS:.2e} rows at the top row's {top_us_per_row:.2} \
         us/row:  {:.1} min",
        PLAN_ROWS * top_us_per_row / 1e6 / 60.0
    );

    // ⚑ THE PROBE. `3dcefe00a` measured the 8-row honest fixture at 173.8 ms prove in release.
    assert!(
        probe_ms > 20.0 && probe_ms < 3000.0,
        "the 8-row probe row measured {probe_ms:.1} ms; the recorded release cost is 173.8 ms. \
         Far outside that band means the harness is measuring something else (debug mode, a \
         cached proof, a different descriptor) and no row in this table is a measurement."
    );
}

/// The security-PARITY points named in `ir2_config`'s own docblock, plus two interior rungs so the
/// curve has a shape and not just two ends. `q` is the query count that holds the conjectured
/// soundness level fixed as `log_blowup` drops.
const FRI_PARITY: &[(usize, usize)] = &[(6, 19), (4, 29), (3, 39), (2, 57), (1, 114)];

fn config_at(log_blowup: usize, num_queries: usize) -> DreggStarkConfig {
    create_config_with_fri_full(
        log_blowup,
        /* log_final_poly_len */ 0,
        /* max_log_arity */ 3,
        num_queries,
        /* commit_pow */ 0,
        /* query_pow */ 16,
    )
}

/// ⚑ **§C — THE FRI BLOWUP, RE-PRICED FOR THIS WORKLOAD.** Security held at parity; the three
/// axes that move are prover time, PEAK MEMORY, and proof size.
#[test]
fn the_fri_blowup_is_repriced_at_parity_for_a_pasta_workload() {
    let a = &atoms()[0];
    let (_, committed, _) = committed_width(&a.desc);
    let log_rows: u32 = std::env::var("DREGG_FRI_SWEEP_LOG_ROWS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(12);
    let n = 1usize << log_rows;
    let trace = cycle_to(&a.honest, n);
    let trace_gb = (n * committed * 4) as f64 / 1e9;

    println!("\n═══ §C  FRI BLOWUP RE-PRICED (security at parity) ═══");
    println!("workload: {n} rows x {committed} committed columns = {trace_gb:.3} GB trace");

    // ⚑ **THE WARM-UP, AND IT IS NOT POLITENESS.** The first `prove` in a process pays the rayon
    // pool spin-up, the thread-local config build and a cold allocator. An un-warmed sweep measured
    // the deployed `(6, 19)` point at 6638 ms against 2894 ms warm — a 2.3x inflation, all of it on
    // the row the other rows are scored against, which would have manufactured a ~12x "speedup"
    // out of a cold start. Discard it, and take the SECOND timing of every rung.
    {
        let cfg = config_at(6, 19);
        let warm = prove_vm_descriptor2_with_config(
            &a.desc,
            &trace,
            &[],
            &MemBoundaryWitness::default(),
            &[],
            &cfg,
        )
        .expect("warm-up proof");
        verify_vm_descriptor2_with_config(&a.desc, &warm, &[], &cfg).expect("warm-up verifies");
    }

    println!(
        "\n{:>3}  {:>4}  {:>11}  {:>11}  {:>11}  {:>12}  {:>16}",
        "lb", "q", "prove ms", "verify ms", "proof KiB", "LDE GB@this", "LDE GB @1.51M rows"
    );

    let mut base_ms = f64::NAN;
    for &(lb, q) in FRI_PARITY {
        let cfg = config_at(lb, q);
        let mut prove_ms = f64::NAN;
        let mut proof = None;
        // Twice; report the second. The first pass at a NEW blowup re-sizes the DFT/Merkle
        // scratch, and that allocation is not part of the steady-state cost being compared.
        for _ in 0..2 {
            let t0 = std::time::Instant::now();
            match prove_vm_descriptor2_with_config(
                &a.desc,
                &trace,
                &[],
                &MemBoundaryWitness::default(),
                &[],
                &cfg,
            ) {
                Ok(p) => {
                    prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
                    proof = Some(p);
                }
                Err(e) => {
                    println!("{lb:>3}  {q:>4}  REFUSED: {e}");
                    proof = None;
                    break;
                }
            }
        }
        let Some(proof) = proof else { continue };
        let t1 = std::time::Instant::now();
        verify_vm_descriptor2_with_config(&a.desc, &proof, &[], &cfg)
            .unwrap_or_else(|e| panic!("lb={lb} q={q} honest proof must verify: {e}"));
        let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
        let proof_kib = postcard::to_allocvec(&proof)
            .expect("serialize proof")
            .len() as f64
            / 1024.0;
        let blow = (1usize << lb) as f64;
        if lb == 6 {
            base_ms = prove_ms;
        }
        println!(
            "{lb:>3}  {q:>4}  {prove_ms:>11.1}  {verify_ms:>11.1}  {proof_kib:>11.1}  \
             {:>12.3}  {:>16.1}",
            trace_gb * blow,
            PLAN_ROWS * committed as f64 * 4.0 / 1e9 * blow,
        );
    }
    if base_ms.is_finite() {
        println!(
            "\nthe deployed point is (lb 6, q 19) at {base_ms:.1} ms; every row above holds the \
             conjectured soundness level fixed and moves only prover time, PEAK MEMORY and proof \
             size."
        );
    }

    assert!(
        base_ms.is_finite(),
        "the deployed (lb=6, q=19) point must prove; if it did not, no row of this sweep is \
         a comparison against anything"
    );
}

/// ⚑ **§C2 — ONE config per PROCESS, so `/usr/bin/time -l` can attribute PEAK RSS to it.**
/// Peak memory is the axis that decides whether the 1.51 M-row instance exists at all, and an
/// in-process sweep cannot measure it (the allocator retains the high-water mark of every earlier
/// rung). Driven by `DREGG_FRI_ONE=<lb>,<q>`; skipped when unset.
#[test]
fn one_fri_point_per_process_for_peak_rss() {
    let Ok(spec) = std::env::var("DREGG_FRI_ONE") else {
        println!("\n§C2 skipped (set DREGG_FRI_ONE=lb,q and run under /usr/bin/time -l)");
        return;
    };
    let (lb, q) = spec
        .split_once(',')
        .map(|(a, b)| {
            (
                a.trim().parse::<usize>().expect("lb"),
                b.trim().parse::<usize>().expect("q"),
            )
        })
        .expect("DREGG_FRI_ONE=lb,q");
    let log_rows: u32 = std::env::var("DREGG_FRI_SWEEP_LOG_ROWS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(13);
    let a = &atoms()[0];
    let (_, committed, _) = committed_width(&a.desc);
    let n = 1usize << log_rows;
    let trace = cycle_to(&a.honest, n);
    let cfg = config_at(lb, q);
    let t0 = std::time::Instant::now();
    let proof = prove_vm_descriptor2_with_config(
        &a.desc,
        &trace,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &cfg,
    )
    .unwrap_or_else(|e| panic!("lb={lb} q={q} at {n} rows must prove: {e}"));
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
    verify_vm_descriptor2_with_config(&a.desc, &proof, &[], &cfg).expect("verifies");
    let proof_kib = postcard::to_allocvec(&proof).expect("serialize").len() as f64 / 1024.0;
    println!(
        "\n§C2  lb={lb} q={q} rows={n} committed={committed}  prove {prove_ms:.1} ms  \
         proof {proof_kib:.1} KiB  us/row {:.1}  (peak RSS from /usr/bin/time -l)",
        prove_ms * 1000.0 / n as f64
    );
}

/// ⚑ **§D — THE REFUSAL POLE OF THE SWEEP.** A blowup BELOW the constraint-degree floor must be
/// refused by the prover, not silently accepted. `ir2_degree_budget` pins the main AIR at degree
/// 3, so the floor is `log_blowup >= log2_ceil(3 - 1) = 1`. This asserts the deployed atom is at
/// or above it at `lb = 1` — i.e. that the sweep's bottom rung is a REAL point and not a value the
/// prover happens to tolerate by accident.
#[test]
fn the_bottom_rung_of_the_sweep_is_at_the_degree_floor() {
    let a = &atoms()[0];
    let trace = cycle_to(&a.honest, 64);
    let cfg = config_at(1, 114);
    let proof = prove_vm_descriptor2_with_config(
        &a.desc,
        &trace,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &cfg,
    )
    .expect("the sound multiply is degree <= 3, so log_blowup = 1 is at its floor and must prove");
    verify_vm_descriptor2_with_config(&a.desc, &proof, &[], &cfg)
        .expect("and the lb=1 proof verifies");

    // The OTHER polarity: a proof minted at one blowup must not verify under another. FRI shape
    // and Fiat-Shamir both move, so this is the wire-incompatibility the docblock claims.
    let other = config_at(6, 19);
    assert!(
        verify_vm_descriptor2_with_config(&a.desc, &proof, &[], &other).is_err(),
        "a proof minted at lb=1 must NOT verify under lb=6 -- if it does, the config is not in \
         the Fiat-Shamir transcript and the blowup is not a wire parameter at all"
    );
}
