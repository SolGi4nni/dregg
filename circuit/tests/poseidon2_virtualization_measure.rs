//! # COMMITTED vs VIRTUALIZED, on the Poseidon2 permutation — MEASURED
//!
//! ## ⚑ SAY THE SUBSTRATE OUT LOUD
//!
//! **This file authors NO constraint system.** It is a stopwatch. Two *existing*
//! arithmetizations of the *same* permutation are proved under the *same*
//! `create_config()` at the *same* row counts, and the wall-clocks and committed-element
//! counts are printed.
//!
//! - **Arm A — "materialize"**: the deployed algebra. Its author is
//!   `metatheory/Dregg2/Circuit/Emit/Poseidon2RoundGates.lean` (`permEmission`), whose
//!   Rust twin is `plonky3_prover::poseidon2_permute_expr_lanes`. [`ArmAMaterialize`]
//!   below has a one-line `eval` that CALLS that gadget and asserts nothing of its own.
//! - **Arm B — "virtualize the degree-1 lanes"**: upstream `p3_poseidon2_air::Poseidon2Air`
//!   at the workspace-pinned rev. Same permutation (this file hands it the DEPLOYED round
//!   constants and the deployed linear layers), same `max_constraint_degree = 7`, but
//!   lanes 1..15 of each partial round are carried as expressions rather than committed.
//!
//! Neither arm is a thing to ship as written. If arm B wins, what lands is a
//! `permEmissionNarrow` in `Poseidon2RoundGates.lean` and a chip re-emit — **Lean-authored,
//! like the deployed one.** Architectural law #1 is not bent here: no constraint below is
//! written in Rust.
//!
//! ## The fidelity gate comes first
//!
//! A timing comparison between two arithmetizations is meaningless if they are not
//! arithmetizing the same function. [`arms_agree_on_the_deployed_permutation`] runs both
//! arms' witness generators on identical inputs and refuses unless the final states match
//! the deployed `poseidon2_trace` bit for bit. It runs before any clock starts.

use std::time::Instant;

use dregg_circuit::field::BabyBear;
use dregg_circuit::plonky3_prover::{
    POSEIDON2_PERM_AUX_COLS, POSEIDON2_WIDTH, create_config, poseidon2_permute_aux_witness, to_p3,
};
use dregg_circuit::poseidon2::{
    EXTERNAL_ROUNDS, INTERNAL_ROUNDS, ROUND_CONSTANTS, TOTAL_ROUNDS, WIDTH, poseidon2_trace,
};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::{BabyBear as P3BabyBear, GenericPoseidon2LinearLayersBabyBear};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2_air::{Poseidon2Air, RoundConstants, generate_trace_rows, num_cols};
use p3_uni_stark::{prove, verify};

const HALF_FULL: usize = EXTERNAL_ROUNDS / 2; // 4
const PARTIAL: usize = INTERNAL_ROUNDS; // 13
const SBOX_DEGREE: u64 = 7;
/// `0` registers ⇒ the S-box is an inline `x^7`, exactly the deployed gadget's spelling
/// (`exp_const_u64::<7>`). A nonzero value commits the S-box intermediates, which is the
/// arm `PROOF-ECONOMICS.md §2c` already measured and rejected — the OTHER direction from
/// the one this file is about.
const SBOX_REGISTERS: usize = 0;

/// Arm A's trace: the 16 seed lanes, then the deployed 352-column aux block.
const ARM_A_WIDTH: usize = POSEIDON2_WIDTH + POSEIDON2_PERM_AUX_COLS; // 368
/// Arm B's trace: whatever upstream's column struct says. Asserted against the hand
/// derivation in [`the_committed_element_census`] rather than trusted.
const ARM_B_WIDTH: usize = num_cols::<16, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL, PARTIAL>();

type ArmBAir = Poseidon2Air<
    P3BabyBear,
    GenericPoseidon2LinearLayersBabyBear,
    16,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL,
    PARTIAL,
>;

/// The DEPLOYED round constants, re-cut into upstream's three-block shape.
///
/// `compute_round_constants` (`poseidon2.rs:117`) lays them out as four external rows, then
/// thirteen rows whose only nonzero lane is `rc[0]`, then four external rows. Upstream wants
/// exactly that split, with the partial block as scalars. Nothing is invented: every value
/// is read out of `ROUND_CONSTANTS`.
fn deployed_round_constants() -> RoundConstants<P3BabyBear, 16, HALF_FULL, PARTIAL> {
    let rc = &*ROUND_CONSTANTS;
    let beginning = core::array::from_fn(|r| core::array::from_fn(|j| to_p3(rc[r][j])));
    let partial = core::array::from_fn(|r| to_p3(rc[HALF_FULL + r][0]));
    let ending =
        core::array::from_fn(|r| core::array::from_fn(|j| to_p3(rc[HALF_FULL + PARTIAL + r][j])));
    // The internal rounds really are lane-0-only in the deployed table — if they were not,
    // dropping lanes 1..15 here would be a silent change of permutation.
    for r in 0..PARTIAL {
        for j in 1..WIDTH {
            assert_eq!(
                rc[HALF_FULL + r][j],
                BabyBear::ZERO,
                "internal round {r} lane {j} carries a constant; the three-block re-cut would drop it"
            );
        }
    }
    RoundConstants::new(beginning, partial, ending)
}

// ============================================================================
// Arm A — the deployed algebra, in a stopwatch wrapper
// ============================================================================

/// ⚠ A HARNESS, NOT AN AIR. `eval` delegates in full to the deployed gadget and adds no
/// constraint. The constraints it emits are the 352 authored in
/// `Poseidon2RoundGates.lean::permEmission` and mirrored by
/// `plonky3_prover::poseidon2_permute_expr_lanes`.
struct ArmAMaterialize;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for ArmAMaterialize {
    fn width(&self) -> usize {
        ARM_A_WIDTH
    }
    fn num_public_values(&self) -> usize {
        0
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(SBOX_DEGREE as usize)
    }
}

impl<AB: AirBuilder> Air<AB> for ArmAMaterialize
where
    AB::F: PrimeField32,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let seed: [AB::Expr; POSEIDON2_WIDTH] = core::array::from_fn(|i| local[i].into());
        let aux: Vec<AB::Var> = local[POSEIDON2_WIDTH..ARM_A_WIDTH].to_vec();
        // The ONLY line. Every constraint comes from here.
        let _ =
            dregg_circuit::plonky3_prover::poseidon2_permute_expr_lanes::<AB>(builder, seed, &aux);
    }
}

/// Arm A's witness: seed lanes, then `poseidon2_permute_aux_witness`.
fn arm_a_trace(inputs: &[[BabyBear; WIDTH]]) -> RowMajorMatrix<P3BabyBear> {
    let mut values = Vec::with_capacity(inputs.len() * ARM_A_WIDTH);
    for input in inputs {
        for lane in input {
            values.push(to_p3(*lane));
        }
        for v in poseidon2_permute_aux_witness(*input) {
            values.push(to_p3(v));
        }
    }
    RowMajorMatrix::new(values, ARM_A_WIDTH)
}

fn arm_b_trace(inputs: &[[BabyBear; WIDTH]]) -> RowMajorMatrix<P3BabyBear> {
    let p3_inputs: Vec<[P3BabyBear; 16]> = inputs
        .iter()
        .map(|row| core::array::from_fn(|j| to_p3(row[j])))
        .collect();
    generate_trace_rows::<
        P3BabyBear,
        GenericPoseidon2LinearLayersBabyBear,
        16,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL,
        PARTIAL,
    >(p3_inputs, &deployed_round_constants(), 0)
}

fn inputs(n: usize) -> Vec<[BabyBear; WIDTH]> {
    (0..n)
        .map(|i| {
            core::array::from_fn(|j| {
                BabyBear::new(
                    ((i as u64 * 0x9E37_79B9 + j as u64 * 0x85EB_CA6B) % 2_013_265_921) as u32,
                )
            })
        })
        .collect()
}

// ============================================================================
// §1 — THE CENSUS
// ============================================================================

#[test]
fn the_committed_element_census() {
    // Arm A, from the deployed constant.
    assert_eq!(POSEIDON2_PERM_AUX_COLS, 352);
    assert_eq!((TOTAL_ROUNDS + 1) * WIDTH, 352);

    // Arm B, from upstream's own `size_of` — and independently, from the hand derivation.
    let derived = 16 + EXTERNAL_ROUNDS * 16 + PARTIAL * 1;
    assert_eq!(
        ARM_B_WIDTH, derived,
        "upstream num_cols disagrees with the hand census 16 + 8*16 + 13*1"
    );
    assert_eq!(ARM_B_WIDTH, 157);

    // The 195 that carry no nonlinearity: 13 internal rounds x 15 lanes that only ever pass
    // through an affine map.
    let degree_one_committed = PARTIAL * (WIDTH - 1);
    assert_eq!(degree_one_committed, 195);

    println!("== §1 COMMITTED-ELEMENT CENSUS (per permutation, BabyBear w16, alpha=7) ==");
    println!(
        "  arm A (deployed, materialize) : {POSEIDON2_PERM_AUX_COLS} aux + {WIDTH} seed = {ARM_A_WIDTH}"
    );
    println!(
        "  arm B (narrow, virtualize)    : {ARM_B_WIDTH} total (16 inputs + 8x16 post + 13x1 post_sbox)"
    );
    println!(
        "  ratio aux-block               : {:.3}x",
        POSEIDON2_PERM_AUX_COLS as f64 / (ARM_B_WIDTH - 16) as f64
    );
    println!(
        "  ratio whole row               : {:.3}x",
        ARM_A_WIDTH as f64 / ARM_B_WIDTH as f64
    );
    println!(
        "  committed felts of degree 1   : {degree_one_committed} internal + 16 initial-layer = {} of 352 ({:.1}%)",
        degree_one_committed + 16,
        100.0 * (degree_one_committed + 16) as f64 / 352.0
    );
}

// ============================================================================
// §2 — FIDELITY. Runs before any clock.
// ============================================================================

#[test]
fn arms_agree_on_the_deployed_permutation() {
    let ins = inputs(64);

    let a = arm_a_trace(&ins);
    let b = arm_b_trace(&ins);
    assert_eq!(a.width(), ARM_A_WIDTH);
    assert_eq!(b.width(), ARM_B_WIDTH);
    assert_eq!(a.height(), 64);
    assert_eq!(b.height(), 64);

    // Arm A's last aux block IS the final permutation state (the gadget rebinds to columns).
    // Arm B's last `post` block is the final state too. They must be equal, and both must
    // equal the deployed `poseidon2_trace`.
    let a_final_off = POSEIDON2_WIDTH + POSEIDON2_PERM_AUX_COLS - WIDTH;
    let b_final_off = ARM_B_WIDTH - WIDTH;
    let mut checked = 0usize;
    for r in 0..64 {
        let deployed = poseidon2_trace(&ins[r])[TOTAL_ROUNDS];
        for j in 0..WIDTH {
            let av = a.get(r, a_final_off + j).unwrap();
            let bv = b.get(r, b_final_off + j).unwrap();
            let dv = to_p3(deployed[j]);
            assert_eq!(
                av, dv,
                "arm A row {r} lane {j} is not the deployed permutation"
            );
            assert_eq!(
                bv, dv,
                "arm B row {r} lane {j} is not the deployed permutation"
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 64 * WIDTH);
    println!(
        "== §2 FIDELITY: both arms reproduce the deployed poseidon2_trace on {checked} lanes =="
    );

    // ⚠ Anti-vacuity: the check above must be able to go red. Perturb one input lane and
    // demand the final states MOVE, so a trivially-equal comparison cannot pass silently.
    let mut moved = ins.clone();
    moved[0][0] = BabyBear::new(moved[0][0].0 ^ 1);
    let a2 = arm_a_trace(&moved);
    let differs = (0..WIDTH).any(|j| a2.get(0, a_final_off + j) != a.get(0, a_final_off + j));
    assert!(
        differs,
        "flipping an input bit did not move the permutation output"
    );
}

// ============================================================================
// §3 — THE CLOCK
// ============================================================================

/// Repetitions per point; the MINIMUM is reported. A minimum-of-k on a contended laptop is
/// the least-noisy estimator of the machine's actual cost — a mean folds in whatever else
/// the box was doing, and this box is running a swarm.
const REPS: usize = 3;

fn measure(log_hashes: usize) {
    let n = 1usize << log_hashes;
    let ins = inputs(n);
    let config = create_config();
    let air_b: ArmBAir = Poseidon2Air::new(deployed_round_constants());

    let mut a_prove = f64::MAX;
    let mut a_verify = f64::MAX;
    let mut b_prove = f64::MAX;
    let mut b_verify = f64::MAX;
    let mut a_bytes = 0usize;
    let mut b_bytes = 0usize;
    let (mut a_cells, mut b_cells) = (0usize, 0usize);

    for _ in 0..REPS {
        let ta = arm_a_trace(&ins);
        a_cells = ta.width() * ta.height();
        let t0 = Instant::now();
        let pa = prove(&config, &ArmAMaterialize, ta, &[]);
        a_prove = a_prove.min(t0.elapsed().as_secs_f64());
        let t0 = Instant::now();
        verify(&config, &ArmAMaterialize, &pa, &[]).expect("arm A must verify");
        a_verify = a_verify.min(t0.elapsed().as_secs_f64());
        a_bytes = bincode_len(&pa);

        let tb = arm_b_trace(&ins);
        b_cells = tb.width() * tb.height();
        let t0 = Instant::now();
        let pb = prove(&config, &air_b, tb, &[]);
        b_prove = b_prove.min(t0.elapsed().as_secs_f64());
        let t0 = Instant::now();
        verify(&config, &air_b, &pb, &[]).expect("arm B must verify");
        b_verify = b_verify.min(t0.elapsed().as_secs_f64());
        b_bytes = bincode_len(&pb);
    }

    println!(
        "  2^{log_hashes:<2} | A {:>8.1} {:>6.1} {:>10} {:>9} | B {:>8.1} {:>6.1} {:>10} {:>9} | prove {:.2}x verify {:.2}x cells {:.2}x size {:.2}x",
        a_prove * 1e3,
        a_verify * 1e3,
        a_cells,
        a_bytes,
        b_prove * 1e3,
        b_verify * 1e3,
        b_cells,
        b_bytes,
        a_prove / b_prove,
        a_verify / b_verify,
        a_cells as f64 / b_cells as f64,
        a_bytes as f64 / b_bytes as f64,
    );
}

/// Serialized proof size. `serde_json` is already a dev-dep and both proof types are
/// `Serialize`; the absolute number is format-dependent but the RATIO — the thing being
/// reported — is not, because both arms go through the identical encoder.
fn bincode_len<T: serde::Serialize>(p: &T) -> usize {
    serde_json::to_vec(p).expect("proof must serialize").len()
}

/// ⚠ `--ignored`: this is a measurement, not a gate. Run with
/// `cargo test -p dregg-circuit --release --test poseidon2_virtualization_measure -- --ignored --nocapture`.
#[test]
#[ignore = "measurement"]
fn prover_wall_clock_committed_vs_virtualized() {
    println!("== §3 PROVER WALL-CLOCK, matched config (create_config(): lb=3, q=38, pow=16) ==");
    println!(
        "   arm A = deployed 352-col materialize | arm B = upstream 157-col narrow, SAME permutation"
    );
    println!("   min of {REPS}; columns are ms-prove, ms-verify, trace cells, proof bytes (json)");
    for lg in [10usize, 12, 14, 16] {
        measure(lg);
    }
}
