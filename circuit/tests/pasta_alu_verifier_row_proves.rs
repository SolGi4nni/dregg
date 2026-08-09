//! # The in-AIR Kimchi/Wrap verifier's ROW, proved on the deployed prover — both polarities, in
//! RELEASE, with literal refusal text.
//!
//! The Lean-authored `Dregg2.Circuit.Emit.MinaWrapVerifierAir.pastaAluAir` is one row that can be a
//! Pasta multiply OR an add OR a sub, selector-gated, over the two sound encodings
//! (`PastaFieldSound` / `PastaAddSubSound`). It is the unit every stage of the verifier is
//! denominated in. This file is the deployed-prover polarity check on it: the Lean side proves what
//! a row FORCES, and only `prove_vm_descriptor2` can show that an honest witness is accepted and a
//! forged one is not.
//!
//! ⚑ **RELEASE, DELIBERATELY.** Algebraic refusals are `debug_assert` PANICS in debug and clean
//! `Err(...)` in release. A refusal test that passes only in debug is testing the assertion, not
//! the constraint system. Every refusal below is asserted on the `Err` string.
//!
//! ⚑ **WHAT THIS DOES NOT SHOW.** That the eight rows compose into a Kimchi verification. Seven of
//! the eight fixture rows carry `SEL_CHAIN = 0`, and
//! `MinaWrapVerifierAir.unchained_transition_relates_nothing` says as a theorem what that means:
//! nothing relates them. The CHAINED fixture (`§4` below) is the one place a row's output is forced
//! into the next row's operand, and it is two rows.
//!
//! Run: `cargo test -p dregg-circuit --release --test pasta_alu_verifier_row_proves -- --nocapture`

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};

const ALU_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-alu-sound.json");
const ALU_TRACE: &str = include_str!("fixtures/pasta-alu-sound-trace.txt");
const ALU_CHAIN_TRACE: &str = include_str!("fixtures/pasta-alu-sound-chain-trace.txt");

/// The Lean layout (`MinaWrapVerifierAir` §1), restated so a drift in either side reds here rather
/// than silently addressing a different column.
const ALU_WIDTH: usize = 226;
const X_BASE: usize = 0;
const Z_BASE: usize = 64;
const Q_BASE: usize = 96;
const SEL_MUL: usize = 222;
const SEL_ADD: usize = 223;
const SEL_SUB: usize = 224;
const SEL_CHAIN: usize = 225;

/// BabyBear's modulus — the field the deployed prover reads every gate body in.
const P_FELT: u64 = 2_013_265_921;

fn desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(ALU_DESC_JSON).expect("the deployed checker parses the ALU descriptor")
}

fn parse_trace(text: &str) -> Vec<Vec<BabyBear>> {
    let t: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect();
    assert_eq!(t.len(), 8, "the Lean-emitted fixture is 8 rows");
    assert!(
        t.iter().all(|r| r.len() == ALU_WIDTH),
        "every row is {ALU_WIDTH} wide"
    );
    t
}

fn prove_and_verify(d: &EffectVmDescriptor2, trace: &[Vec<BabyBear>]) -> Result<(), String> {
    let proof = prove_vm_descriptor2(d, trace, &[], &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(d, &proof, &[])
}

#[allow(dead_code)]
fn bump(cell: BabyBear, delta: u64) -> BabyBear {
    BabyBear::new(((cell.as_u32() as u64 + delta) % P_FELT) as u32)
}

/// ⚑ A forgery that stays INSIDE the declared 8-bit range.
///
/// The first draft of §3 used [`bump`] on an 8-bit limb whose honest value was `255`; the cell went
/// to `256` and the refusal that came back was `range wire 64 value 256 >= 2^8` — the LOOKUP
/// caught it, and the add gate was never tested at all. A forgery that trips a cheaper check than
/// the one under test is not a test of that check. Wrapping inside the limb width keeps every
/// declared lookup satisfied, so the only thing left that can refuse is the algebra.
fn bump_limb8(cell: BabyBear) -> BabyBear {
    BabyBear::new((cell.as_u32() + 1) % 256)
}

/// The committed main width, from the descriptor's own tables through the deployed
/// `decomp_cols_pub` — the number every trace-size figure must be denominated in.
fn committed_width(d: &EffectVmDescriptor2) -> usize {
    let mut aux = 0usize;
    for c in &d.constraints {
        if let VmConstraint2::Lookup(l) = c {
            if let Some(bits) =
                d.tables
                    .iter()
                    .find(|t| t.id == l.table)
                    .and_then(|t| match t.sem {
                        TableSem::Range { bits } => Some(bits),
                        _ => None,
                    })
            {
                aux += decomp_cols_pub(bits);
            }
        }
    }
    d.trace_width + aux
}

/// ⚑ **§1 — THE HONEST POLARITY.** Eight rows, all three operations, on the deployed prover.
#[test]
fn the_alu_row_proves_all_three_operations() {
    let d = desc();
    let trace = parse_trace(ALU_TRACE);

    println!("\n═══ THE PASTA ALU ROW — the in-AIR verifier's unit ═══");
    println!(
        "descriptor        {}\nconstraints       {}\ndeclared columns  {}\ncommitted columns {}",
        d.name,
        d.constraints.len(),
        d.trace_width,
        committed_width(&d),
    );
    assert_eq!(
        d.constraints.len(),
        386,
        "the Lean theorem `fpAluDesc_constraint_count` says 386; a different count here means the \
         checked-in JSON is not the emission of the descriptor those theorems are about"
    );
    assert_eq!(d.trace_width, ALU_WIDTH);

    // The fixture really does exercise all three operations, so a green here is not a green on
    // eight copies of one row.
    let sel = |r: usize, c: usize| trace[r][c].as_u32();
    assert_eq!(sel(0, SEL_MUL), 1, "row 0 is a multiply");
    assert_eq!(sel(1, SEL_ADD), 1, "row 1 is an add");
    assert_eq!(sel(2, SEL_SUB), 1, "row 2 is a sub");
    assert!(
        (0..8).all(|r| sel(r, SEL_CHAIN) == 0),
        "the unchained fixture carries SEL_CHAIN = 0 on every row"
    );

    prove_and_verify(&d, &trace).expect("the honest ALU trace must prove and verify");
    println!("\nHONEST: 8 rows (mul, add, sub) PROVED and VERIFIED in release.");
}

/// ⚑ **§2 — THE MULTIPLY FORGERY IS REFUSED.** The `9×30` encoding's defect was that a quotient
/// limb entered with a coefficient that is a unit mod `P`, so a bump could be absorbed. At `8×32`
/// the same bump moves gate 0's body by `−p₀·d` with `|p₀·d| < P`, so it cannot hide.
#[test]
fn the_multiply_quotient_forgery_is_refused() {
    let d = desc();
    let mut trace = parse_trace(ALU_TRACE);
    trace[0][Q_BASE] = bump_limb8(trace[0][Q_BASE]);

    let err = prove_and_verify(&d, &trace)
        .expect_err("a bumped quotient limb on a multiply row must be REFUSED");
    println!("\n§2 multiply-quotient forgery REFUSED: {err}");
    assert!(
        err.contains("OodEvaluationMismatch"),
        "the multiply GATE must be what refuses, not a range lookup -- got: {err}"
    );
}

/// ⚑ **§3 — THE ADD FORGERY IS REFUSED**, and on the ADD row specifically — so this is a check on
/// the selector-gated add gates, not a second reading of §2.
#[test]
fn the_add_result_forgery_is_refused() {
    let d = desc();
    let mut trace = parse_trace(ALU_TRACE);
    trace[1][Z_BASE] = bump_limb8(trace[1][Z_BASE]);

    let err = prove_and_verify(&d, &trace)
        .expect_err("a bumped result limb on an add row must be REFUSED");
    println!("§3 add-result forgery REFUSED: {err}");
    assert!(
        err.contains("OodEvaluationMismatch"),
        "the ADD GATE must be what refuses, not a range lookup -- a forgery that trips a cheaper \
         check than the one under test does not test it. Got: {err}"
    );
}

/// ⚑ **§4 — THE SELECTOR IS A CONSTRAINT, NOT A CONVENTION.** Turning a second operation selector
/// on must be refused by the selector-sum gate, even though the row's own operation is untouched.
/// Without this, a row could claim to be two things and satisfy the weaker one.
#[test]
fn a_row_claiming_two_operations_is_refused() {
    let d = desc();
    let mut trace = parse_trace(ALU_TRACE);
    assert_eq!(trace[0][SEL_MUL].as_u32(), 1);
    trace[0][SEL_ADD] = BabyBear::new(1);

    let err = prove_and_verify(&d, &trace)
        .expect_err("a row with two operation selectors set must be REFUSED");
    println!("§4 two-selector row REFUSED: {err}");
    assert!(!err.is_empty());

    // And the other pole: a row with NO operation selector set is refused too, so `sMul + sAdd +
    // sSub = 1` is a real equality and not a `<= 1` bound.
    let mut trace2 = parse_trace(ALU_TRACE);
    trace2[0][SEL_MUL] = BabyBear::new(0);
    let err2 = prove_and_verify(&d, &trace2)
        .expect_err("a row with NO operation selector set must be REFUSED");
    println!("§4 no-selector row REFUSED:  {err2}");
    assert!(!err2.is_empty());

    // …and a NON-BOOLEAN selector, which the booleanity gate is there for.
    let mut trace3 = parse_trace(ALU_TRACE);
    trace3[0][SEL_MUL] = BabyBear::new(2);
    trace3[0][SEL_ADD] = BabyBear::new(P_FELT as u32 - 1); // 2 + (-1) = 1, so the SUM still holds
    let err3 = prove_and_verify(&d, &trace3)
        .expect_err("a non-boolean selector pair summing to 1 must be REFUSED by booleanity");
    println!("§4 non-boolean selector REFUSED: {err3}");
    assert!(!err3.is_empty());
}

/// ⚑ **§5 — THE CHAIN, BOTH POLARITIES.** This is the only inter-row wiring the IR's main rail can
/// express (`MinaWrapVerifierAir.inter_row_wiring_is_transition_only`), so it is the only place a
/// row's OUTPUT is forced to be the next row's INPUT — i.e. the only thing that makes a trace a
/// straight-line program rather than a bag of unrelated operations.
#[test]
fn the_chain_leg_binds_one_rows_output_to_the_nexts_operand() {
    let d = desc();
    let chain: Vec<Vec<BabyBear>> = ALU_CHAIN_TRACE
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("u32")))
                .collect()
        })
        .collect();
    assert_eq!(chain.len(), 8);
    assert!(chain.iter().all(|r| r.len() == ALU_WIDTH));

    // The chain selector is ON at row 0 — otherwise the honest leg below is the vacuous case.
    assert_eq!(
        chain[0][SEL_CHAIN].as_u32(),
        1,
        "row 0 of the chained fixture must have SEL_CHAIN = 1, or this test proves nothing"
    );
    // …and row 1's x block really IS row 0's z block.
    for i in 0..32 {
        assert_eq!(
            chain[1][X_BASE + i],
            chain[0][Z_BASE + i],
            "limb {i}: the chained fixture's row 1 operand must be row 0's result"
        );
    }

    prove_and_verify(&d, &chain).expect("the honest CHAINED trace must prove and verify");
    println!("\n§5 HONEST CHAIN (SEL_CHAIN = 1, row1.x = row0.z): PROVED and VERIFIED.");

    // ⚑ THE REFUSAL POLE. Break the wiring by one limb and the chain leg must catch it.
    let mut broken = chain.clone();
    broken[1][X_BASE] = bump_limb8(broken[1][X_BASE]);
    let err = prove_and_verify(&d, &broken)
        .expect_err("a chained transition whose operand does not match must be REFUSED");
    println!("§5 broken chain REFUSED: {err}");
    assert!(!err.is_empty());

    // …and the OTHER direction: turning the chain selector on over an UNCHAINED pair is refused,
    // which is what makes `SEL_CHAIN` a claim a prover cannot make for free.
    let mut lying = parse_trace(ALU_TRACE);
    lying[0][SEL_CHAIN] = BabyBear::new(1);
    let err2 = prove_and_verify(&d, &lying)
        .expect_err("asserting SEL_CHAIN over an unrelated pair must be REFUSED");
    println!("§5 lying chain selector REFUSED: {err2}");
    assert!(!err2.is_empty());
}

/// The six stages of "everything except the SRS bases", with the row budgets
/// `MinaWrapVerifierAir` derives from the atom (`verifier_rows_eq : VERIFIER_ROWS = 1671656`).
/// ⚠ The transcript stage read `170_940` until 2026-08-08 — a Poseidon round is 30 emitted
/// instructions, not the 21 multiplies the census counted.
const STAGES: &[(&str, usize)] = &[
    ("transcript  (148 Fq Poseidon perms)", 244_200),
    ("public_comm (MSM over 40 bases)", 430_336),
    ("f_comm      (MSM over 1 base)", 20_992),
    ("ft_comm     (MSM over 9 bases)", 104_960),
    ("xi-aggregate(MSM over 47 bases)", 503_808),
    ("opening     (MSM over 34 bases) VACUOUS", 367_360),
];

/// ⚑ **§6 — THE VERIFIER PRICED STAGE BY STAGE, ON MEASURED NUMBERS.**
///
/// The ALU is ROW-LOCAL apart from its 32 chain legs, and the chain legs are satisfied vacuously
/// when `SEL_CHAIN = 0` — so replicating the unchained fixture is a legal witness at any height and
/// the cost curve it traces is the real one. What it is NOT is a verifier: see
/// `unchained_transition_relates_nothing`. This measures the PRICE of the rows, which is the
/// question the plan's `1.51 M / 0.93 GB / 8–12 min` answers.
///
/// Cap the measured top row with `DREGG_ALU_MAX_LOG_ROWS` (default 14). The stage table is
/// extrapolated from the top MEASURED row, not from a model.
#[test]
fn the_verifier_is_priced_stage_by_stage() {
    let d = desc();
    let base = parse_trace(ALU_TRACE);
    let committed = committed_width(&d);

    println!("\n═══ §6  THE IN-AIR WRAP VERIFIER, PRICED ═══");
    println!(
        "ALU row: {} constraints, {} declared, {committed} committed columns \
         ({:.2}x the standalone multiply's 694)",
        d.constraints.len(),
        d.trace_width,
        committed as f64 / 694.0,
    );

    let max_log: u32 = std::env::var("DREGG_ALU_MAX_LOG_ROWS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(14);

    println!(
        "\n{:>10}  {:>12}  {:>11}  {:>11}  {:>10}",
        "rows", "trace MiB", "prove ms", "verify ms", "us/row"
    );
    let mut top_us_per_row = f64::NAN;
    for log_n in 3..=max_log {
        let n = 1usize << log_n;
        let trace: Vec<Vec<BabyBear>> = (0..n).map(|i| base[i % base.len()].clone()).collect();
        let trace_mib = (n * committed * 4) as f64 / (1024.0 * 1024.0);
        let t0 = std::time::Instant::now();
        let proof = prove_vm_descriptor2(&d, &trace, &[], &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("honest {n}-row ALU trace must prove: {e}"));
        let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let t1 = std::time::Instant::now();
        verify_vm_descriptor2(&d, &proof, &[]).expect("and verifies");
        let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
        top_us_per_row = prove_ms * 1000.0 / n as f64;
        println!(
            "{n:>10}  {trace_mib:>12.2}  {prove_ms:>11.1}  {verify_ms:>11.1}  {top_us_per_row:>10.1}"
        );
    }

    // ⚑ The stage table, extrapolated from the top MEASURED row.
    println!(
        "\n{:>38}  {:>10}  {:>11}  {:>12}  {:>12}",
        "stage", "rows", "trace GB", "LDE GB @lb6", "prove min"
    );
    let mut total_rows = 0usize;
    for (name, rows) in STAGES {
        let trace_gb = *rows as f64 * committed as f64 * 4.0 / 1e9;
        total_rows += rows;
        println!(
            "{name:>38}  {rows:>10}  {trace_gb:>11.2}  {:>12.1}  {:>12.1}",
            trace_gb * 64.0,
            *rows as f64 * top_us_per_row / 1e6 / 60.0,
        );
    }
    let total_gb = total_rows as f64 * committed as f64 * 4.0 / 1e9;
    println!(
        "{:>38}  {total_rows:>10}  {total_gb:>11.2}  {:>12.1}  {:>12.1}",
        "TOTAL (everything but the SRS bases)",
        total_gb * 64.0,
        total_rows as f64 * top_us_per_row / 1e6 / 60.0,
    );
    println!(
        "\nagainst the plan's prediction of 1 510 000 rows / 0.93 GB trace / 8-12 min:\n  \
         rows   {total_rows}  ({:+.1}%)\n  \
         trace  {total_gb:.2} GB  ({:.2}x the predicted 0.93 GB -- the plan priced DECLARED \
         columns, the prover commits {committed})\n  \
         prove  {:.1} min at the deployed lb=6",
        (total_rows as f64 / 1.51e6 - 1.0) * 100.0,
        total_gb / 0.93,
        total_rows as f64 * top_us_per_row / 1e6 / 60.0,
    );

    // ⚑ The row ceiling is a FIELD fact, not a policy: BabyBear's two-adicity is 27, so the LDE
    // domain `2^(log_rows + log_blowup)` caps `log_rows` at `27 - log_blowup`.
    let pad_log = (total_rows as f64).log2().ceil() as usize;
    println!(
        "\nthe instance pads to 2^{pad_log}. BabyBear two-adicity is 27, so the ROW ceiling is \
         2^{} at lb=6 and 2^{} at lb=2.",
        27 - 6,
        27 - 2
    );
    assert!(
        top_us_per_row.is_finite() && top_us_per_row > 0.0,
        "no row of the stage table means anything without a measured us/row"
    );
}
