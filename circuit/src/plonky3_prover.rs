//! Plonky3 configuration and reusable Poseidon2 chip-interpreter machinery.
//!
//! This module provides a production-grade prover using Plonky3's `p3-uni-stark`
//! framework with BabyBear field, Poseidon2 hashing, and FRI polynomial commitment.
//!
//! The former Rust-authored Merkle AIR is
//! retired under architectural law #1. Merkle membership now routes through the
//! descriptor emitted by `MerkleMembership4aryEmit.lean`; this module retains
//! configuration, witness-generation compatibility, and the generic Poseidon2
//! chip implementation used by the assured descriptor interpreter.
//!
//! ## Configuration
//!
//! - Field: BabyBear (p = 2^31 - 2^27 + 1)
//! - Hash: Poseidon2 (width 16, alpha=7, 4+4 external + 13 internal rounds)
//!   Parameters from Plonky3/Poseidon2 paper with 128-bit security proofs.
//! - PCS: TwoAdicFriPcs with Poseidon2 Merkle trees
//! - Extension field: BinomialExtensionField<BabyBear, 4> (degree-4 extension)
//! - DFT: Radix2DitParallel (parallel NTT)
//! - FRI: log_blowup=3 (8x), 38 queries, 16 PoW bits (the `PROD_FRI_*` consts / `create_config`;
//!   ≈130-bit REFUTED-conjecture capacity baseline, a 73-bit Johnson QUERY column — which is the
//!   `m → ∞` idealisation and drops BCIKS20's commit-phase term `ε_C`, so it is not a soundness
//!   headline — and a 116-bit per-fold posture at the NEAR-CAPACITY radius. Every figure is
//!   computed by the VERIFIED Lean ledger, not here: see create_config's note and
//!   `circuit-prove/tests/fri_params_soundness_budget.rs`)

use std::sync::LazyLock;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{Proof, StarkConfig, prove, verify};

use crate::field::BabyBear;
use crate::poseidon2::{
    EXTERNAL_ROUNDS, INTERNAL_DIAG, INTERNAL_ROUNDS, ROUND_CONSTANTS, TOTAL_ROUNDS, WIDTH,
    poseidon2_trace,
};

// ============================================================================
// Type definitions for our Plonky3 configuration
// ============================================================================

/// The Poseidon2 permutation over width-16 arrays.
type Perm16 = Poseidon2BabyBear<16>;

/// Extension field: degree-[`PROD_EXT_DEGREE`] extension of BabyBear. The degree is written as the
/// exported const, not as a bare `4`, so the FRI ledger gate can PIN it: `ext_deg` fixes the
/// challenge-space size `|F| = babyBearP ^ ext_deg`, which is a divisor of every per-fold soundness
/// number (`Dregg2.Circuit.FriLedger.friLedger`). It was previously reachable only as a type
/// argument, which is why the old gate named it "the remaining un-pinned modeled parameter".
type EF = BinomialExtensionField<P3BabyBear, PROD_EXT_DEGREE>;

/// The DFT implementation (parallel radix-2).
type DreggDft = Radix2DitParallel<P3BabyBear>;

// ============================================================================
// Configuration builder
// ============================================================================

/// Create the Plonky3 STARK configuration with production parameters.
/// Internal type aliases matching Plonky3's proven test configuration.
type TestHash = PaddingFreeSponge<Perm16, 16, 8, 8>;
type TestCompress = TruncatedPermutation<Perm16, 2, 8, 16>;
type TestMmcs = MerkleTreeMmcs<
    <P3BabyBear as Field>::Packing,
    <P3BabyBear as Field>::Packing,
    TestHash,
    TestCompress,
    2,
    8,
>;
type TestChallenger = DuplexChallenger<P3BabyBear, Perm16, 16, 8>;
type TestPcs =
    TwoAdicFriPcs<P3BabyBear, DreggDft, TestMmcs, ExtensionMmcs<P3BabyBear, EF, TestMmcs>>;

/// The actual STARK config type used (matching Plonky3's own test setup).
pub type DreggStarkConfig = StarkConfig<TestPcs, EF, TestChallenger>;

/// A Plonky3 proof object for dregg circuits.
pub type DreggProof = Proof<DreggStarkConfig>;

/// The PRODUCTION v1 FRI knobs ([`create_config`]), exported so the checked-in params→bits budget
/// gate (`circuit-prove/tests/fri_params_soundness_budget.rs`) can hand them to the VERIFIED Lean
/// ledger (`@[export] dregg_fri_ledger` over `Dregg2.Circuit.FriLedger.friLedger`) and PIN them
/// against the Lean-modeled `FriLedgerSound.prodV1Config`. The gate does not derive soundness numbers
/// from these — the metatheory does, and the gate reports what it returns. Moving any of these moves
/// the wire (FRI shape + Fiat–Shamir) — one rotation epoch.
pub const PROD_FRI_LOG_BLOWUP: usize = 3;
pub const PROD_FRI_LOG_FINAL_POLY_LEN: usize = 0;
pub const PROD_FRI_MAX_LOG_ARITY: usize = 3;
pub const PROD_FRI_NUM_QUERIES: usize = 38;
pub const PROD_FRI_QUERY_POW_BITS: usize = 16;
/// The challenge extension degree — `|F| = babyBearP ^ PROD_EXT_DEGREE ≈ 2^123.6`. It is the
/// denominator of every per-fold proximity-gap bound, so it is a soundness knob as much as the five
/// above; it is exported (and used to build [`EF`]) so it cannot drift from the modeled `extDeg`
/// unnoticed.
pub const PROD_EXT_DEGREE: usize = 4;

pub fn create_config() -> DreggStarkConfig {
    // log_blowup must be >= log2_ceil(max_constraint_degree - 1).
    // For Poseidon2 S-box (degree 7): log2_ceil(6) = 3, so log_blowup >= 3.
    //
    // The QUERY LEDGER at these settings (two columns; neither is "the soundness"):
    //   capacity column (REFUTED conjecture): ~log_blowup bits/query
    //     => 38 * 3 + 16 PoW = 130 — a knob-drift baseline only. The up-to-capacity
    //     correlated-agreement conjecture is disproved (Crites-Stewart, eprint 2025/2046;
    //     Kambire, arXiv 2604.09724).
    //   Johnson query column (list-decoding to sqrt(rate)): ~log_blowup/2 bits/query
    //     => 38 * 1.5 + 16 PoW = 73 — the QUERY COLUMN, not "proven soundness". It is the
    //     m -> infinity idealisation of BCIKS20's alpha = sqrt(rho)*(1 + 1/2m) and DROPS the
    //     commit-phase term eps_C of Thm 8.3 (eps_FRI = eps_C + alpha^s). eps_C is Lean's
    //     `FriLedger.friCommitLedger`; it depends on the TRACE HEIGHT, which is not an FRI
    //     knob, and it binds. Composing as ethSTARK eq. (20) does
    //     (lambda >= min{-log2 eps_C, zeta - s*log2 alpha} - 1) reads ~70 at the deployed
    //     wrap's |D^(0)| = 2^12, not 73.
    // (both additionally capped by the degree-4 extension field, ~2^124, and the
    // Poseidon2 commitment hash.) See docs/PROOF-ECONOMICS.md for the measured
    // size/prover-time tradeoff of these knobs: q = 50 → 38 (the rotation's
    // planned ride-along) keeps the conjectured bound ≥ 128 bits and was
    // measured at −23% proof size. Proofs are NOT interchangeable across this
    // bump (FRI shape + Fiat–Shamir differ) — it lands inside the one
    // VK/commitment rotation epoch by design.
    //
    // The `≥ 128 conjectured` drift margin (and the PROVEN Johnson / per-fold floors) are
    // ENFORCED by `circuit-prove/tests/fri_params_soundness_budget.rs` over these exported
    // knobs — a knob drift below a floor is a red test, not a silent downgrade. That gate
    // derives no soundness number itself: it hands these knobs to the VERIFIED Lean ledger
    // (`@[export] dregg_fri_ledger` over `Dregg2.Circuit.FriLedger.friLedger`) and reports
    // what comes back, and it PINS them against the Lean-modeled `FriLedgerSound.prodV1Config`.
    create_config_with_fri(
        PROD_FRI_LOG_BLOWUP,
        PROD_FRI_LOG_FINAL_POLY_LEN,
        PROD_FRI_MAX_LOG_ARITY,
        PROD_FRI_NUM_QUERIES,
        PROD_FRI_QUERY_POW_BITS,
    )
}

/// Build a `DreggStarkConfig` with explicit FRI knobs. The production
/// configuration is [`create_config`]; this parameterized constructor exists so
/// the proof-economics measurements (`tests/proof_economics.rs`) can prove the
/// SAME statement under alternative `(log_blowup, log_final_poly_len,
/// max_log_arity, num_queries, query_pow_bits)` settings and measure the real
/// size/time deltas. Proofs from different configs are NOT interchangeable
/// (FRI shape and Fiat–Shamir differ), so non-default configs must never leak
/// onto the wire.
pub fn create_config_with_fri(
    log_blowup: usize,
    log_final_poly_len: usize,
    max_log_arity: usize,
    num_queries: usize,
    query_proof_of_work_bits: usize,
) -> DreggStarkConfig {
    let perm16 = default_babybear_poseidon2_16();

    let hash = PaddingFreeSponge::new(perm16.clone());
    let compress = TruncatedPermutation::new(perm16.clone());
    let val_mmcs = TestMmcs::new(hash, compress, 0);

    let challenge_mmcs = ExtensionMmcs::<P3BabyBear, EF, _>::new(val_mmcs.clone());

    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len,
        max_log_arity,
        num_queries,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits,
        mmcs: challenge_mmcs,
    };

    let dft = Radix2DitParallel::default();
    let pcs = TwoAdicFriPcs::new(dft, val_mmcs, fri_params);

    let challenger = TestChallenger::new(perm16);
    StarkConfig::new(pcs, challenger)
}

// ============================================================================
// Poseidon2 round constants as P3BabyBear (computed once, cached)
// ============================================================================

/// Round constants converted to P3BabyBear for use in constraint evaluation.
static P3_ROUND_CONSTANTS: LazyLock<Vec<[P3BabyBear; WIDTH]>> = LazyLock::new(|| {
    ROUND_CONSTANTS
        .iter()
        .map(|rc| {
            let mut p3_rc = [P3BabyBear::ZERO; WIDTH];
            for i in 0..WIDTH {
                p3_rc[i] = P3BabyBear::new(rc[i].0);
            }
            p3_rc
        })
        .collect()
});

/// Internal diagonal converted to P3BabyBear.
static P3_INTERNAL_DIAG: LazyLock<[P3BabyBear; WIDTH]> = LazyLock::new(|| {
    let mut p3_diag = [P3BabyBear::ZERO; WIDTH];
    for i in 0..WIDTH {
        p3_diag[i] = P3BabyBear::new(INTERNAL_DIAG[i].0);
    }
    p3_diag
});

// ============================================================================
// Trace layout constants
// ============================================================================

/// Number of auxiliary columns per round (full 16-element post-state).
const ROUND_COLS: usize = WIDTH; // 16

/// Half the number of external rounds.
const HALF_EXTERNAL: usize = EXTERNAL_ROUNDS / 2; // 4

/// Total auxiliary columns for Poseidon2 intermediate states:
/// (1 + TOTAL_ROUNDS) * 16 = 352
const POSEIDON2_AUX_COLS: usize = (TOTAL_ROUNDS + 1) * ROUND_COLS; // 352

/// Total trace width:
/// - 5 witness columns: current, sib0, sib1, sib2, position
/// - 352 auxiliary columns for Poseidon2 states
/// - 1 parent column (== final_state[0])
///
/// Total: 358
pub const P3_TRACE_WIDTH: usize = 5 + POSEIDON2_AUX_COLS + 1; // 358

/// Offset where round states begin in the trace row.
const ROUND_STATES_OFFSET: usize = 5;

/// Column index of the parent hash.
const PARENT_COL: usize = P3_TRACE_WIDTH - 1; // 245

// ============================================================================
// Algebraic linear layers over AB::Expr
// ============================================================================

/// Apply the external linear layer (MDSMat4 + wider) over abstract expressions.
fn external_linear_layer_expr<AB: AirBuilder>(state: &mut [AB::Expr; WIDTH])
where
    AB::F: PrimeField32,
{
    // Apply 4x4 MDS [2,3,1,1] to each chunk of 4
    for cs in (0..WIDTH).step_by(4) {
        let x0 = state[cs].clone();
        let x1 = state[cs + 1].clone();
        let x2 = state[cs + 2].clone();
        let x3 = state[cs + 3].clone();
        let t01 = x0.clone() + x1.clone();
        let t23 = x2.clone() + x3.clone();
        let t0123 = t01.clone() + t23.clone();
        let t01123 = t0123.clone() + x1.clone();
        let t01233 = t0123 + x3.clone();
        state[cs] = t01123.clone() + t01;
        state[cs + 1] = t01123 + x2.clone() + x2;
        state[cs + 2] = t01233.clone() + t23;
        state[cs + 3] = t01233 + x0.clone() + x0;
    }
    // Wider: add column sums
    let sums: [AB::Expr; 4] = core::array::from_fn(|k| {
        let mut s = state[k].clone();
        for j in (4..WIDTH).step_by(4) {
            s += state[j + k].clone();
        }
        s
    });
    for i in 0..WIDTH {
        state[i] = state[i].clone() + sums[i % 4].clone();
    }
}

/// Apply the internal linear layer (matching poseidon2.rs) over abstract expressions.
///
/// Poseidon2 internal layer: x_i' = sum + (d_i - 1) * x_i
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
fn internal_linear_layer_expr<AB: AirBuilder>(
    state: &mut [AB::Expr; WIDTH],
    diag: &[P3BabyBear; WIDTH],
) where
    AB::F: PrimeField32,
{
    // Compute sum of all state elements
    let mut sum: AB::Expr = state[0].clone();
    for i in 1..WIDTH {
        sum += state[i].clone();
    }

    // x_i' = sum + (d_i - 1) * x_i
    for i in 0..WIDTH {
        let d_i_minus_1 = diag[i] - P3BabyBear::ONE;
        let coeff = AB::F::from_u32(d_i_minus_1.as_canonical_u32());
        state[i] = sum.clone() + state[i].clone() * coeff;
    }
}

// ============================================================================
// Reusable Poseidon2 permutation gadget (real p3 arithmetization)
// ============================================================================

/// Number of aux columns one Poseidon2 permutation consumes in a trace row:
/// `(1 + TOTAL_ROUNDS) * 16`. Exposed so callers (e.g. the DSL p3 AIR) can size
/// their trace and slot per-hash aux blocks.
pub const POSEIDON2_PERM_AUX_COLS: usize = POSEIDON2_AUX_COLS; // 352

/// The Poseidon2 permutation width (16).
pub const POSEIDON2_WIDTH: usize = WIDTH;

/// Emit the real Poseidon2-permutation constraints (round-by-round, the SAME
/// arithmetization the emitted `MerkleMembership4aryEmit.lean` descriptor uses) for an input `state`, binding
/// each round's output to the `aux` witness columns (length must be
/// [`POSEIDON2_PERM_AUX_COLS`]). Returns the permutation output state[0] as an
/// `AB::Expr` (the hash digest for a sponge with rate ≥ 1).
///
/// `aux[j]` for the first block is the post-initial-linear-layer state; the
/// remaining `TOTAL_ROUNDS` blocks of 16 are the per-round outputs. This is the
/// genuine in-circuit Poseidon2 — NOT a concrete recompute — so the resulting
/// digest constraint is algebraically enforced by the audited p3 verifier.
pub fn poseidon2_permute_expr<AB: AirBuilder>(
    builder: &mut AB,
    state: [AB::Expr; WIDTH],
    aux: &[AB::Var],
) -> AB::Expr
where
    AB::F: PrimeField32,
{
    let lanes = poseidon2_permute_expr_lanes::<AB>(builder, state, aux);
    lanes[0].clone()
}

/// Like [`poseidon2_permute_expr`] but returns the first 8 lanes of the
/// permutation output (`state[0..8]`) instead of only the squeezed `state[0]`.
///
/// Every one of the 16 final-state lanes is already equality-constrained to the
/// genuine permutation output (`aux[last_block + j]`) by the round-by-round
/// arithmetization — this just EXPOSES the first 8 of them. The lanes are
/// genuinely 8 distinct field elements (the final permutation state), NOT eight
/// copies of `state[0]`. Used by the IR-v2 chip table to widen its bus tuple's
/// output block from 1 to 8 (`CHIP_RATE`-faithful squeeze). The aux block and
/// every internal constraint are byte-identical to [`poseidon2_permute_expr`];
/// only the return arity differs.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn poseidon2_permute_expr_lanes<AB: AirBuilder>(
    builder: &mut AB,
    mut state: [AB::Expr; WIDTH],
    aux: &[AB::Var],
) -> [AB::Expr; 8]
where
    AB::F: PrimeField32,
{
    assert_eq!(
        aux.len(),
        POSEIDON2_AUX_COLS,
        "poseidon2_permute_expr: aux must be {POSEIDON2_AUX_COLS} columns"
    );
    let rc = &*P3_ROUND_CONSTANTS;
    let diag = &*P3_INTERNAL_DIAG;

    let mut off = 0usize;

    // Initial linear layer.
    external_linear_layer_expr::<AB>(&mut state);
    for j in 0..WIDTH {
        let a: AB::Expr = aux[off + j].into();
        builder.assert_eq(state[j].clone(), a.clone());
        state[j] = a;
    }
    off += ROUND_COLS;

    // First half external rounds.
    for round in 0..HALF_EXTERNAL {
        for j in 0..WIDTH {
            let rc_f = AB::F::from_u32(rc[round][j].as_canonical_u32());
            state[j] = state[j].clone() + rc_f;
        }
        for j in 0..WIDTH {
            state[j] = state[j].clone().exp_const_u64::<7>();
        }
        external_linear_layer_expr::<AB>(&mut state);
        for j in 0..WIDTH {
            let a: AB::Expr = aux[off + j].into();
            builder.assert_eq(state[j].clone(), a.clone());
            state[j] = a;
        }
        off += ROUND_COLS;
    }

    // Internal rounds.
    for round in 0..INTERNAL_ROUNDS {
        let rc_idx = HALF_EXTERNAL + round;
        let rc0_f = AB::F::from_u32(rc[rc_idx][0].as_canonical_u32());
        state[0] = state[0].clone() + rc0_f;
        state[0] = state[0].clone().exp_const_u64::<7>();
        internal_linear_layer_expr::<AB>(&mut state, diag);
        for j in 0..WIDTH {
            let a: AB::Expr = aux[off + j].into();
            builder.assert_eq(state[j].clone(), a.clone());
            state[j] = a;
        }
        off += ROUND_COLS;
    }

    // Second half external rounds.
    for round in 0..HALF_EXTERNAL {
        let rc_idx = HALF_EXTERNAL + INTERNAL_ROUNDS + round;
        for j in 0..WIDTH {
            let rc_f = AB::F::from_u32(rc[rc_idx][j].as_canonical_u32());
            state[j] = state[j].clone() + rc_f;
        }
        for j in 0..WIDTH {
            state[j] = state[j].clone().exp_const_u64::<7>();
        }
        external_linear_layer_expr::<AB>(&mut state);
        for j in 0..WIDTH {
            let a: AB::Expr = aux[off + j].into();
            builder.assert_eq(state[j].clone(), a.clone());
            state[j] = a;
        }
        off += ROUND_COLS;
    }

    core::array::from_fn(|i| state[i].clone())
}

/// Compute the full intermediate-state aux block (length
/// [`POSEIDON2_PERM_AUX_COLS`]) for a concrete input `state`, matching exactly
/// what [`poseidon2_permute_expr`] constrains. Witness generators call this to
/// fill the per-hash aux columns.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn poseidon2_permute_aux_witness(input: [BabyBear; WIDTH]) -> Vec<BabyBear> {
    let round_states = poseidon2_trace(&input);
    let mut out = Vec::with_capacity(POSEIDON2_AUX_COLS);
    for round_idx in 0..=TOTAL_ROUNDS {
        for j in 0..WIDTH {
            out.push(round_states[round_idx][j]);
        }
    }
    debug_assert_eq!(out.len(), POSEIDON2_AUX_COLS);
    out
}

// NOTE on S-box arithmetization (measured 2026-06-11, docs/PROOF-ECONOMICS.md §2c):
// a 1-register variant of the gadget above (committed cube `s3 = x³` per S-box, so no
// constraint exceeds degree 3 — the `sbox_registers = 1` shape the IR-v2 chip
// descriptor params describe) was built and measured against this inline-x⁷ form.
// It is worse at every security-parity FRI point: +141 aux columns per permutation
// ⇒ +25.8 KiB on the transfer proof at (lb=3, q=38), and the lower blowup it enables
// loses outright at constant conjectured soundness (queries dominate IR-v2 proof
// size; the winning direction is HIGHER blowup with FEWER queries). The inline
// gadget therefore stays; re-run `effect_vm_ir2_size_measure::ir2_fri_grid` before
// revisiting.

// ============================================================================
// Trace generation for the sound Poseidon2 AIR
// ============================================================================

/// Generate the execution trace for the sound Merkle Poseidon2 AIR.
///
/// Each row contains:
/// - 5 witness columns (current, sib0, sib1, sib2, position)
/// - 240 auxiliary columns (30 rounds x 8 state elements)
/// - 1 parent column
///
/// The auxiliary columns store the actual intermediate Poseidon2 states
/// computed during hash evaluation, which the AIR constrains algebraically.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn generate_sound_merkle_trace(
    leaf_hash: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);
    assert!(depth >= 2, "need at least 2 levels for STARK");

    let padded = depth.next_power_of_two();
    let mut trace = Vec::with_capacity(padded);
    let mut current = leaf_hash;

    for i in 0..depth {
        let pos = positions[i];
        assert!(pos < 4, "position must be 0..3");

        let mut children = [BabyBear::ZERO; 4];
        let mut sib_idx = 0;
        for j in 0..4u8 {
            if j == pos {
                children[j as usize] = current;
            } else {
                children[j as usize] = siblings[i][sib_idx];
                sib_idx += 1;
            }
        }

        // Compute full Poseidon2 trace
        let mut input_state = [BabyBear::ZERO; WIDTH];
        input_state[0] = children[0];
        input_state[1] = children[1];
        input_state[2] = children[2];
        input_state[3] = children[3];
        input_state[4] = BabyBear::new(4); // arity domain separator

        let round_states = poseidon2_trace(&input_state);
        let parent = round_states[TOTAL_ROUNDS][0];

        let mut row = Vec::with_capacity(P3_TRACE_WIDTH);
        row.push(current);
        row.push(siblings[i][0]);
        row.push(siblings[i][1]);
        row.push(siblings[i][2]);
        row.push(BabyBear::new(pos as u32));

        // Auxiliary: (1 + TOTAL_ROUNDS) x WIDTH elements
        for round_idx in 0..=TOTAL_ROUNDS {
            for j in 0..WIDTH {
                row.push(round_states[round_idx][j]);
            }
        }

        row.push(parent);
        debug_assert_eq!(row.len(), P3_TRACE_WIDTH);
        trace.push(row);
        current = parent;
    }

    let root = current;

    // For non-power-of-2 depths: extend the hash chain with additional levels.
    // Each extension level has current = prev_parent, siblings = [0,0,0], position = 0.
    // This forms a valid hash chain that satisfies all constraints.
    let mut extended_root = root;
    for _ in depth..padded {
        let mut ext_input = [BabyBear::ZERO; WIDTH];
        ext_input[0] = extended_root;
        ext_input[4] = BabyBear::new(4);

        let ext_states = poseidon2_trace(&ext_input);
        let ext_parent = ext_states[TOTAL_ROUNDS][0];

        let mut ext_row = Vec::with_capacity(P3_TRACE_WIDTH);
        ext_row.push(extended_root);
        ext_row.push(BabyBear::ZERO);
        ext_row.push(BabyBear::ZERO);
        ext_row.push(BabyBear::ZERO);
        ext_row.push(BabyBear::ZERO); // position = 0

        for round_idx in 0..=TOTAL_ROUNDS {
            for j in 0..WIDTH {
                ext_row.push(ext_states[round_idx][j]);
            }
        }
        ext_row.push(ext_parent);

        trace.push(ext_row);
        extended_root = ext_parent;
    }

    // The public root is the parent of the last trace row.
    let final_root = if depth < padded { extended_root } else { root };

    let public_inputs = vec![leaf_hash, final_root];
    (trace, public_inputs)
}

// ============================================================================
// Prove / Verify API
// ============================================================================

/// Convert our BabyBear values to Plonky3's BabyBear.
pub fn to_p3(val: BabyBear) -> P3BabyBear {
    P3BabyBear::new(val.0)
}

/// Convert Plonky3's BabyBear back to ours.
#[allow(dead_code)]
pub fn from_p3(val: P3BabyBear) -> BabyBear {
    BabyBear(val.as_canonical_u32())
}

/// Convert our trace to a Plonky3 RowMajorMatrix.
pub fn trace_to_matrix(trace: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
    let width = trace[0].len();
    let values: Vec<P3BabyBear> = trace
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, width)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Minimal AIR with degree-7 constraint to test that our config supports high-degree AIRs.
    /// If this passes but the emitted membership descriptor fails, the bug is in the descriptor, not the chip.
    struct MinimalDegree7Air;

    impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for MinimalDegree7Air {
        fn width(&self) -> usize {
            2 // [x, x^7]
        }
        fn num_public_values(&self) -> usize {
            0
        }
        fn max_constraint_degree(&self) -> Option<usize> {
            Some(7)
        }
    }

    impl<AB: AirBuilder> Air<AB> for MinimalDegree7Air
    where
        AB::F: PrimeField32,
    {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let local = main.current_slice();
            let x: AB::Expr = local[0].into();
            let x7_witness: AB::Expr = local[1].into();
            // Constraint: x^7 == x7_witness
            let x7_computed = x.exp_const_u64::<7>();
            builder.assert_eq(x7_computed, x7_witness);
        }
    }

    #[test]
    fn plonky3_minimal_degree7_prove_verify() {
        // Create a 4-row trace where col0 = some values, col1 = col0^7
        let config = create_config();
        let air = MinimalDegree7Air;

        let values: Vec<P3BabyBear> = [5u32, 17, 42, 100]
            .iter()
            .flat_map(|&v| {
                let x = P3BabyBear::new(v);
                let x7 = x.exp_const_u64::<7>();
                [x, x7]
            })
            .collect();
        let matrix = RowMajorMatrix::new(values, 2);
        let public: Vec<P3BabyBear> = vec![];

        let proof = prove(&config, &air, matrix, &public);
        let result = verify(&config, &air, &proof, &public);
        assert!(
            result.is_ok(),
            "Minimal degree-7 AIR (4 rows) failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn plonky3_minimal_degree7_more_rows() {
        // Try with 256 rows to rule out small-trace issues
        let config = create_config();
        let air = MinimalDegree7Air;

        let values: Vec<P3BabyBear> = (1u32..=256)
            .flat_map(|v| {
                let x = P3BabyBear::new(v * 7 + 3);
                let x7 = x.exp_const_u64::<7>();
                [x, x7]
            })
            .collect();
        let matrix = RowMajorMatrix::new(values, 2);
        let public: Vec<P3BabyBear> = vec![];

        let proof = prove(&config, &air, matrix, &public);
        let result = verify(&config, &air, &proof, &public);
        assert!(
            result.is_ok(),
            "Minimal degree-7 AIR (256 rows) failed: {:?}",
            result.err()
        );
    }

    /// MulAir: a^6 * b == c (degree 7), copied from Plonky3's own test
    struct MulAir7;

    impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for MulAir7 {
        fn width(&self) -> usize {
            3 // [a, b, c]
        }
    }

    impl<AB: AirBuilder> Air<AB> for MulAir7 {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let local = main.current_slice();
            let a: AB::Expr = local[0].into();
            let b: AB::Expr = local[1].into();
            let c: AB::Expr = local[2].into();
            // Constraint: a^6 * b == c  (total degree 7)
            builder.assert_zero(a.exp_u64(6) * b - c);
        }
    }

    #[test]
    fn plonky3_mulair7_our_config() {
        let config = create_config();
        let air = MulAir7;

        let values: Vec<P3BabyBear> = (1u32..=16)
            .flat_map(|v| {
                let a = P3BabyBear::new(v * 13 + 7);
                let b = P3BabyBear::new(v * 37 + 11);
                let c = a.exp_u64(6) * b;
                [a, b, c]
            })
            .collect();
        let matrix = RowMajorMatrix::new(values, 3);
        let public: Vec<P3BabyBear> = vec![];

        let proof = prove(&config, &air, matrix, &public);
        let result = verify(&config, &air, &proof, &public);
        assert!(
            result.is_ok(),
            "MulAir7 with our config failed: {:?}",
            result.err()
        );
    }

    /// Parameterized degree AIR: x^D == witness
    struct MinimalDegreeNAir<const D: u64>;

    impl<const D: u64, F: PrimeCharacteristicRing + Sync> BaseAir<F> for MinimalDegreeNAir<D> {
        fn width(&self) -> usize {
            2
        }
        fn num_public_values(&self) -> usize {
            0
        }
    }

    impl<const D: u64, AB: AirBuilder> Air<AB> for MinimalDegreeNAir<D>
    where
        AB::F: PrimeField32,
    {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let local = main.current_slice();
            let x: AB::Expr = local[0].into();
            let xd_witness: AB::Expr = local[1].into();
            let xd_computed = x.exp_u64(D);
            builder.assert_zero(xd_computed - xd_witness);
        }
    }

    #[test]
    fn plonky3_minimal_degree2() {
        let config = create_config();
        let air = MinimalDegreeNAir::<2>;

        let values: Vec<P3BabyBear> = (1u32..=16)
            .flat_map(|v| {
                let x = P3BabyBear::new(v);
                let xd = x.exp_u64(2);
                [x, xd]
            })
            .collect();
        let matrix = RowMajorMatrix::new(values, 2);
        let public: Vec<P3BabyBear> = vec![];

        let proof = prove(&config, &air, matrix, &public);
        let result = verify(&config, &air, &proof, &public);
        assert!(
            result.is_ok(),
            "Minimal degree-2 AIR failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn plonky3_minimal_degree3() {
        let config = create_config();
        let air = MinimalDegreeNAir::<3>;

        let values: Vec<P3BabyBear> = (1u32..=16)
            .flat_map(|v| {
                let x = P3BabyBear::new(v);
                let xd = x.exp_u64(3);
                [x, xd]
            })
            .collect();
        let matrix = RowMajorMatrix::new(values, 2);
        let public: Vec<P3BabyBear> = vec![];

        let proof = prove(&config, &air, matrix, &public);
        let result = verify(&config, &air, &proof, &public);
        assert!(
            result.is_ok(),
            "Minimal degree-3 AIR failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn plonky3_minimal_degree4() {
        let config = create_config();
        let air = MinimalDegreeNAir::<4>;
        let values: Vec<P3BabyBear> = (1u32..=16)
            .flat_map(|v| {
                let x = P3BabyBear::new(v);
                [x, x.exp_u64(4)]
            })
            .collect();
        let matrix = RowMajorMatrix::new(values, 2);
        let proof = prove(&config, &air, matrix, &[]);
        let result = verify(&config, &air, &proof, &[]);
        assert!(result.is_ok(), "degree-4 failed: {:?}", result.err());
    }

    #[test]
    fn plonky3_minimal_degree5() {
        let config = create_config();
        let air = MinimalDegreeNAir::<5>;
        let values: Vec<P3BabyBear> = (1u32..=16)
            .flat_map(|v| {
                let x = P3BabyBear::new(v);
                [x, x.exp_u64(5)]
            })
            .collect();
        let matrix = RowMajorMatrix::new(values, 2);
        let proof = prove(&config, &air, matrix, &[]);
        let result = verify(&config, &air, &proof, &[]);
        assert!(result.is_ok(), "degree-5 failed: {:?}", result.err());
    }

    #[test]
    fn plonky3_minimal_degree6() {
        let config = create_config();
        let air = MinimalDegreeNAir::<6>;
        let values: Vec<P3BabyBear> = (1u32..=16)
            .flat_map(|v| {
                let x = P3BabyBear::new(v);
                [x, x.exp_u64(6)]
            })
            .collect();
        let matrix = RowMajorMatrix::new(values, 2);
        let proof = prove(&config, &air, matrix, &[]);
        let result = verify(&config, &air, &proof, &[]);
        assert!(result.is_ok(), "degree-6 failed: {:?}", result.err());
    }
}
