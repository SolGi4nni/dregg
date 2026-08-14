//! # The NARROW Poseidon2 aux witness — bound to the Lean that specifies it, and measured
//!
//! ## ⚑ SAY THE SUBSTRATE OUT LOUD
//!
//! **This file authors NO constraint.** The two arithmetizations it exercises are
//! `metatheory/Dregg2/Circuit/Emit/Poseidon2RoundGates.lean`'s `permEmission` (§5b, the DEPLOYED
//! one) and `permEmissionNarrow` (§8), wrapped as standalone table AIRs by
//! `Dregg2/Circuit/Emit/PermArmTableEmit.lean` and emitted to
//! `circuit/tests/fixtures/perm-arms/`. Every verdict below comes from the **deployed
//! interpreter** — `Ir2Air::LeanTable`, through `table_air_gates_accept` and `prove_batch` — walking
//! those emitted bytes. Nothing here re-implements a gate.
//!
//! What this file DOES author is the thing Lean cannot see: **a Rust witness generator**, and the
//! evidence that it produces what the Lean object binds.
//!
//! ## The gap this closes
//!
//! `permEmissionNarrow` commits 141 aux lanes per permutation where the deployed arm commits 352,
//! at the same `max_constraint_degree = 7`, and §8e proves the two equation systems have the same
//! solutions under the projection. That is a statement about AIRs. The prover writes witnesses, and
//! `poseidon2_permute_aux_witness` writes 352 values — so until a 141-value generator exists the
//! narrow arm cannot be proved at all, and "the Lean is landed" is not "the win is banked".
//!
//! ## What is checked, in order of strength
//!
//! 1. `the_narrow_witness_is_the_lean_projection` — the generator's 141 values ARE the projection
//!    Lean's `narrowAuxWitness` (§8d) names, recomputed here from the WIDE generator's output plus
//!    the deployed round constants. Two independent programs, same numbers.
//! 2. `the_narrow_witness_forces_the_whole_wide_trace` — the lift back. `narrowSat_forces_the_trace`
//!    says the 141 leave nothing free; this runs that reconstruction and demands the 352.
//! 3. `the_lean_narrow_air_accepts_the_rust_witness` — the Lean-emitted 141 gates, walked by the
//!    deployed interpreter, accept the row this generator fills.
//! 4. `every_narrow_column_is_pinned` — ⚠ THE CONSTRUCTIVE FALSIFIER. Each of the 157 columns is
//!    bumped by one, the bump is ASSERTED to have changed the row (a mutation that silently becomes
//!    a no-op is how a falsifier dies quietly), and the AIR must refuse. A column that survives is a
//!    free column, and there are none.
//! 5. The two `#[ignore]`d measurements: per-chip prove/verify/bytes on the two arms under the
//!    deployed FRI knobs, and the deployed transfer batch's committed-matrix census.
//!
//! Run the measurements with:
//! `cargo nextest run -p dregg-circuit --release -E 'binary(poseidon2_narrow_witness)' --run-ignored all`

use std::sync::Arc;

use dregg_circuit::descriptor_ir2::{
    IR2_FRI_COMMIT_POW_BITS, IR2_FRI_LOG_BLOWUP, IR2_FRI_LOG_FINAL_POLY_LEN, IR2_FRI_MAX_LOG_ARITY,
    IR2_FRI_NUM_QUERIES, Ir2Air, MemBoundaryWitness, ir2_airs_and_common_for_config,
    parse_vm_descriptor2, table_air_gates_accept, verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace};
use dregg_circuit::effect_vm_descriptors::descriptor2_for_key;
use dregg_circuit::field::BabyBear;
use dregg_circuit::plonky3_prover::{
    POSEIDON2_PERM_AUX_COLS, POSEIDON2_PERM_AUX_COLS_NARROW, POSEIDON2_WIDTH,
    poseidon2_narrow_base, poseidon2_permute_aux_witness, poseidon2_permute_aux_witness_narrow,
    poseidon2_round_is_external, poseidon2_wide_aux_from_narrow, to_p3,
};
use dregg_circuit::poseidon2::{
    EXTERNAL_ROUNDS, INTERNAL_ROUNDS, Poseidon2State, ROUND_CONSTANTS, TOTAL_ROUNDS, WIDTH,
    poseidon2_trace,
};

use dregg_circuit::table_air::{LeanTableAir, parse_table_air};

use p3_air::BaseAir;
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_batch_stark::{ProverData, StarkInstance, prove_batch, verify_batch};
use p3_matrix::dense::RowMajorMatrix;

/// `HALF_EXTERNAL` — the four opening full rounds. Derived, never transcribed.
const HALF_EXTERNAL_ROUNDS: usize = EXTERNAL_ROUNDS / 2;

// ─────────────────────────────────────────────────────────────────────────────
// The Lean-emitted arms
// ─────────────────────────────────────────────────────────────────────────────

/// The DEPLOYED algebra as a standalone table: 16 seed lanes ‖ 352 aux columns.
const WIDE_ARM_JSON: &str = include_str!("fixtures/perm-arms/dregg-perm-arm-wide-v1.json");
/// The NARROW algebra as a standalone table: 16 seed lanes ‖ 141 aux columns.
const NARROW_ARM_JSON: &str = include_str!("fixtures/perm-arms/dregg-perm-arm-narrow-v1.json");

/// Both arms lay the permutation seed at columns `0..16` and the aux block after it.
const ARM_IN0: usize = 0;
const ARM_AUX0: usize = ARM_IN0 + POSEIDON2_WIDTH;
const WIDE_ARM_WIDTH: usize = ARM_AUX0 + POSEIDON2_PERM_AUX_COLS; // 368
const NARROW_ARM_WIDTH: usize = ARM_AUX0 + POSEIDON2_PERM_AUX_COLS_NARROW; // 157

fn wide_arm() -> LeanTableAir {
    parse_table_air(WIDE_ARM_JSON).expect("the wide arm artifact decodes")
}

fn narrow_arm() -> LeanTableAir {
    parse_table_air(NARROW_ARM_JSON).expect("the narrow arm artifact decodes")
}

/// A handful of inputs, including the two the Lean KAT uses.
fn probe_inputs() -> Vec<[BabyBear; WIDTH]> {
    let mut v = Vec::new();
    v.push(core::array::from_fn(|i| BabyBear::new(i as u32))); // `List.range 16`
    v.push([BabyBear::ZERO; WIDTH]); // `List.replicate 16 0`
    v.push(core::array::from_fn(|i| {
        BabyBear::new(0x1234_5678u32.wrapping_mul(i as u32 + 1) % 2_013_265_921)
    }));
    v.push(core::array::from_fn(|i| {
        BabyBear::new(2_013_265_920 - i as u32) // near the modulus
    }));
    v
}

fn narrow_row(input: [BabyBear; WIDTH]) -> Vec<BabyBear> {
    let mut row = Vec::with_capacity(NARROW_ARM_WIDTH);
    row.extend_from_slice(&input);
    row.extend(poseidon2_permute_aux_witness_narrow(input));
    assert_eq!(row.len(), NARROW_ARM_WIDTH);
    row
}

fn wide_row(input: [BabyBear; WIDTH]) -> Vec<BabyBear> {
    let mut row = Vec::with_capacity(WIDE_ARM_WIDTH);
    row.extend_from_slice(&input);
    row.extend(poseidon2_permute_aux_witness(input));
    assert_eq!(row.len(), WIDE_ARM_WIDTH);
    row
}

// ─────────────────────────────────────────────────────────────────────────────
// 1 — the projection
// ─────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE GENERATORS AGREE.** Lean's `narrowAuxWitness` (§8d) projects the same `permBlocks`
/// trace the wide arm commits: an external round contributes its whole output block, an internal
/// round contributes `(state[0] + rc[r][0])^7`. That projection is recomputed HERE out of
/// `poseidon2_permute_aux_witness`'s 352 values and `ROUND_CONSTANTS`, and compared against
/// `poseidon2_permute_aux_witness_narrow`.
///
/// ⚠ This is the half a Lean theorem cannot reach. §8e relates the two AIRs; it says nothing about
/// two Rust programs, and the narrow arm is unprovable if the generator disagrees with the
/// projection by one column.
#[test]
fn the_narrow_witness_is_the_lean_projection() {
    let rc = &*ROUND_CONSTANTS;
    for input in probe_inputs() {
        let wide = poseidon2_permute_aux_witness(input);
        let narrow = poseidon2_permute_aux_witness_narrow(input);
        assert_eq!(
            wide.len(),
            POSEIDON2_PERM_AUX_COLS,
            "wide arm is 352 values"
        );
        assert_eq!(
            narrow.len(),
            POSEIDON2_PERM_AUX_COLS_NARROW,
            "narrow arm is 141 values"
        );

        // The projection, spelled out of the WIDE vector alone. `wide[b * 16 .. ]` is block `b`:
        // block 0 is the post-initial-linear-layer state, block `r + 1` is round `r`'s output.
        let block = |b: usize, j: usize| wide[b * WIDTH + j];
        let mut expected: Vec<BabyBear> = Vec::with_capacity(POSEIDON2_PERM_AUX_COLS_NARROW);
        for r in 0..TOTAL_ROUNDS {
            assert_eq!(
                expected.len(),
                poseidon2_narrow_base(r),
                "narrow layout: round {r} must start at its own base"
            );
            if poseidon2_round_is_external(r) {
                for j in 0..WIDTH {
                    expected.push(block(r + 1, j));
                }
            } else {
                expected.push(Poseidon2State::sbox(block(r, 0) + rc[r][0]));
            }
        }
        assert_eq!(
            narrow, expected,
            "the narrow generator is not the Lean projection of the wide one"
        );

        // …and the projection really is a 2.5× cut: 211 of the wide arm's values are gone.
        assert_eq!(wide.len() - narrow.len(), 211);
        assert_eq!(
            POSEIDON2_PERM_AUX_COLS_NARROW,
            8 * WIDTH + INTERNAL_ROUNDS,
            "141 = eight external blocks + thirteen single internal lanes"
        );
    }
}

/// The layout the Lean `narrow_blocks_tile` proves in the kernel, checked on the Rust twin:
/// every committed lane of every round lands on its own column, no alias and no gap.
#[test]
fn the_narrow_layout_tiles_exactly() {
    let mut seen = vec![false; POSEIDON2_PERM_AUX_COLS_NARROW];
    for r in 0..TOTAL_ROUNDS {
        let w = if poseidon2_round_is_external(r) {
            WIDTH
        } else {
            1
        };
        for j in 0..w {
            let c = poseidon2_narrow_base(r) + j;
            assert!(
                c < POSEIDON2_PERM_AUX_COLS_NARROW,
                "round {r} lane {j} is out of range"
            );
            assert!(!seen[c], "round {r} lane {j} aliases column {c}");
            seen[c] = true;
        }
    }
    assert!(seen.iter().all(|&b| b), "the narrow layout leaves a gap");
    // The three regions, in the order `narrowBase` puts them.
    assert_eq!(poseidon2_narrow_base(0), 0);
    assert_eq!(poseidon2_narrow_base(HALF_EXTERNAL_ROUNDS), 64);
    assert_eq!(
        poseidon2_narrow_base(HALF_EXTERNAL_ROUNDS + INTERNAL_ROUNDS),
        77
    );
    assert_eq!(poseidon2_narrow_base(TOTAL_ROUNDS - 1), 125);
}

// ─────────────────────────────────────────────────────────────────────────────
// 2 — the lift
// ─────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE 141 LEAVE NOTHING FREE.** `narrowSat_forces_the_trace` (§8e) says the narrow equations
/// force the whole 352-value chain. `poseidon2_wide_aux_from_narrow` is that reconstruction as a
/// program — it never calls `poseidon2_trace` — and it must land on the wide generator's output
/// exactly.
#[test]
fn the_narrow_witness_forces_the_whole_wide_trace() {
    for input in probe_inputs() {
        let narrow = poseidon2_permute_aux_witness_narrow(input);
        let lifted = poseidon2_wide_aux_from_narrow(input, &narrow);
        assert_eq!(
            lifted,
            poseidon2_permute_aux_witness(input),
            "the lift of the narrow witness is not the wide witness"
        );
    }
}

/// Both arms expose the SAME permutation output, and it is the deployed one. `permOutLaneNarrow`
/// moves only the column index; the meaning of the last block does not change.
#[test]
fn both_arms_end_at_the_deployed_permutation() {
    for input in probe_inputs() {
        let deployed = poseidon2_trace(&input)[TOTAL_ROUNDS];
        let wide = poseidon2_permute_aux_witness(input);
        let narrow = poseidon2_permute_aux_witness_narrow(input);
        for j in 0..WIDTH {
            assert_eq!(wide[POSEIDON2_PERM_AUX_COLS - WIDTH + j], deployed[j]);
            assert_eq!(
                narrow[POSEIDON2_PERM_AUX_COLS_NARROW - WIDTH + j],
                deployed[j]
            );
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 3 — the Lean-emitted AIR accepts the Rust witness
// ─────────────────────────────────────────────────────────────────────────────

/// The emitted artifacts are the shapes `PermArmTableEmit` states, decoded by the deployed parser.
#[test]
fn the_emitted_arms_have_the_stated_shape() {
    let w = wide_arm();
    let n = narrow_arm();
    assert_eq!(w.name, "dregg-perm-arm-wide-v1");
    assert_eq!(n.name, "dregg-perm-arm-narrow-v1");
    assert_eq!(w.width, WIDE_ARM_WIDTH);
    assert_eq!(n.width, NARROW_ARM_WIDTH);
    assert_eq!(w.gates.len(), POSEIDON2_PERM_AUX_COLS);
    assert_eq!(n.gates.len(), POSEIDON2_PERM_AUX_COLS_NARROW);
    assert_eq!(w.defs.len(), 1078);
    assert_eq!(n.defs.len(), 1286);
    assert_eq!(w.prep_width, 0);
    assert_eq!(n.prep_width, 0);
    assert!(w.interactions.is_empty() && n.interactions.is_empty());
    // ⚑ The Pareto claim's load-bearing half, read off the deployed interpreter's own degree pass.
    assert_eq!(w.max_degree(), 7, "the deployed arm is degree 7");
    assert_eq!(
        n.max_degree(),
        7,
        "and so is the narrow one — no degree is traded"
    );
}

/// ⚑ **THE BIND.** The Lean-emitted narrow gates, walked by `Ir2Air::LeanTable`, accept the row
/// this file's generator fills — and the wide baseline still does too.
#[test]
fn the_lean_narrow_air_accepts_the_rust_witness() {
    let w = wide_arm();
    let n = narrow_arm();
    for input in probe_inputs() {
        assert!(
            table_air_gates_accept(&w, &[wide_row(input)]),
            "the deployed arm must accept its own generator's row"
        );
        assert!(
            table_air_gates_accept(&n, &[narrow_row(input)]),
            "the NARROW arm must accept `poseidon2_permute_aux_witness_narrow`'s row"
        );
    }
}

/// ⚠ **A witness for the WRONG arm must be refused, not truncated into acceptance.** The narrow
/// arm's first 157 columns are not a prefix of the wide arm's row: column 16 is round 0's output in
/// the narrow layout and the post-initial-linear-layer state in the wide one.
#[test]
fn the_arms_do_not_accept_each_others_witnesses() {
    let n = narrow_arm();
    for input in probe_inputs() {
        let truncated: Vec<BabyBear> = wide_row(input)[..NARROW_ARM_WIDTH].to_vec();
        // Guard the falsifier: the two rows really do differ somewhere in the window.
        assert_ne!(
            truncated,
            narrow_row(input),
            "the wide row's prefix coincides with the narrow row — this probe would be vacuous"
        );
        assert!(
            !table_air_gates_accept(&n, &[truncated]),
            "the narrow arm accepted a truncated WIDE witness"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 4 — the constructive falsifier
// ─────────────────────────────────────────────────────────────────────────────

/// ⚑ **EVERY COLUMN IS PINNED, AND THE MUTATION IS ASSERTED TO HAVE HAPPENED.**
///
/// A falsifier that stops falsifying is this repo's own minted failure class: the perturbation
/// becomes a no-op and the gate stays green while checking nothing. So each bump is *constructed*
/// (`+1` in the field, which is never the identity) and the mutated row is compared against the
/// honest one before its verdict is read.
///
/// The internal-lane columns (`ARM_AUX0 + 64 ..= ARM_AUX0 + 76`) are the ones that matter: those are
/// exactly the thirteen whose fifteen wide siblings no longer exist. If dropping the siblings had
/// left slack, this is where it would show.
#[test]
fn every_narrow_column_is_pinned() {
    let n = narrow_arm();
    let input = probe_inputs()[0];
    let honest = narrow_row(input);
    assert!(
        table_air_gates_accept(&n, &[honest.clone()]),
        "honest baseline"
    );

    let mut free: Vec<usize> = Vec::new();
    for col in 0..NARROW_ARM_WIDTH {
        let mut forged = honest.clone();
        forged[col] += BabyBear::ONE;
        assert_ne!(
            forged[col], honest[col],
            "column {col}: the perturbation did not change the cell — the probe is dead"
        );
        if table_air_gates_accept(&n, &[forged]) {
            free.push(col);
        }
    }
    assert!(
        free.is_empty(),
        "the narrow arm leaves columns {free:?} free — a witness is not pinned there"
    );

    // And the instrument is not always-false: the honest row is still accepted after the sweep.
    assert!(table_air_gates_accept(&n, &[honest]), "instrument sanity");
}

/// The same sweep on the deployed arm, so the narrow result is read against a baseline measured the
/// same way rather than against an expectation.
#[test]
fn every_wide_column_is_pinned() {
    let w = wide_arm();
    let input = probe_inputs()[0];
    let honest = wide_row(input);
    assert!(
        table_air_gates_accept(&w, &[honest.clone()]),
        "honest baseline"
    );
    let mut free: Vec<usize> = Vec::new();
    for col in 0..WIDE_ARM_WIDTH {
        let mut forged = honest.clone();
        forged[col] += BabyBear::ONE;
        assert_ne!(forged[col], honest[col], "column {col}: dead probe");
        if table_air_gates_accept(&w, &[forged]) {
            free.push(col);
        }
    }
    assert!(free.is_empty(), "the wide arm leaves columns {free:?} free");
}

// ─────────────────────────────────────────────────────────────────────────────
// 5 — the measurements
// ─────────────────────────────────────────────────────────────────────────────
//
// ⚑ **THE UNIT IS COUNTS, NOT MILLISECONDS.** This box is shared and heavily loaded, and the two
// things being compared degrade differently under contention (leaf hashing is memory-bound, the
// quotient is compute-bound), so a wall-clock ratio taken here is not evidence — not even as a
// ratio. Everything below is a COUNT: committed cells, Poseidon2 permutations, proof bytes. All
// three are deterministic functions of (config, trace) and reproducible on any box.
//
// The permutation counter is a `Permutation` wrapper that increments before delegating — the same
// instrument `circuit/tests/ir2_phase_profile.rs` §D uses. It is duplicated here rather than shared
// because it is a stopwatch, not an object under test; if a third file wants one, that is the point
// to lift it into the library.
//
// ⚠ `query_proof_of_work_bits` is set to ZERO for every counted run. Grinding is a random search:
// it costs ~2^16 permutations in expectation and a different number on each transcript, which would
// put ±65k of arm-dependent noise on top of the number being compared. The grinding term is
// identical work on both arms, so removing it removes noise and no signal. The deployed knobs are
// otherwise untouched (`lb = 6`, `q = 19`, `log_final_poly_len = 0`, `max_log_arity = 3`).

use std::sync::atomic::{AtomicU64, Ordering};

use dregg_circuit::descriptor_ir2::{UMemBoundaryWitness, prove_vm_descriptor2_for_config};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::Field;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{
    CryptographicPermutation, PaddingFreeSponge, Permutation, TruncatedPermutation,
};
use p3_uni_stark::StarkConfig;

static PERMS: AtomicU64 = AtomicU64::new(0);

type Pack = <P3BabyBear as Field>::Packing;

#[derive(Clone)]
struct CountingPerm(p3_baby_bear::Poseidon2BabyBear<16>);

// One generic impl: the SIMD lane count is recovered from the state's size, which is exact and
// arch-portable (NEON w=4, AVX2 w=8, AVX-512 w=16, scalar w=1 all fall out of `size_of`), so the
// number reported is SCALAR-EQUIVALENT permutations and does not move with the host's vector width.
impl<T: Clone> Permutation<T> for CountingPerm
where
    p3_baby_bear::Poseidon2BabyBear<16>: Permutation<T>,
{
    fn permute_mut(&self, input: &mut T) {
        let lanes =
            (core::mem::size_of::<T>() / (16 * core::mem::size_of::<P3BabyBear>())).max(1) as u64;
        PERMS.fetch_add(lanes, Ordering::Relaxed);
        self.0.permute_mut(input);
    }
}
impl<T: Clone> CryptographicPermutation<T> for CountingPerm where
    p3_baby_bear::Poseidon2BabyBear<16>: CryptographicPermutation<T>
{
}

type CEf = BinomialExtensionField<P3BabyBear, 4>;
type CHash = PaddingFreeSponge<CountingPerm, 16, 8, 8>;
type CCompress = TruncatedPermutation<CountingPerm, 2, 8, 16>;
type CValMmcs = MerkleTreeMmcs<Pack, Pack, CHash, CCompress, 2, 8>;
type CChallengeMmcs = ExtensionMmcs<P3BabyBear, CEf, CValMmcs>;
type CPcs = TwoAdicFriPcs<P3BabyBear, Radix2DitParallel<P3BabyBear>, CValMmcs, CChallengeMmcs>;
type CChallenger = DuplexChallenger<P3BabyBear, CountingPerm, 16, 8>;
type CountingConfig = StarkConfig<CPcs, CEf, CChallenger>;

/// The DEPLOYED FRI shape with the grinding term removed — see the note above.
fn counting_config() -> CountingConfig {
    let perm = CountingPerm(p3_baby_bear::default_babybear_poseidon2_16());
    let hash = CHash::new(perm.clone());
    let compress = CCompress::new(perm.clone());
    let val_mmcs = CValMmcs::new(hash, compress, 0);
    let fri_params = FriParameters {
        log_blowup: IR2_FRI_LOG_BLOWUP,
        log_final_poly_len: IR2_FRI_LOG_FINAL_POLY_LEN,
        max_log_arity: IR2_FRI_MAX_LOG_ARITY,
        num_queries: IR2_FRI_NUM_QUERIES,
        commit_proof_of_work_bits: IR2_FRI_COMMIT_POW_BITS,
        query_proof_of_work_bits: 0,
        mmcs: CChallengeMmcs::new(val_mmcs.clone()),
    };
    let pcs = TwoAdicFriPcs::new(Radix2DitParallel::default(), val_mmcs, fri_params);
    StarkConfig::new(pcs, CChallenger::new(perm))
}

fn json_len<T: serde::Serialize>(p: &T) -> usize {
    serde_json::to_vec(p).expect("proof serializes").len()
}

/// What one arm costs at `rows` permutations: committed cells, prove permutations, verify
/// permutations, proof bytes. Every one of the four is deterministic.
struct ArmCount {
    cells: usize,
    prove_perms: u64,
    verify_perms: u64,
    bytes: usize,
}

fn count_arm(
    air: &LeanTableAir,
    rows: usize,
    fill: &dyn Fn([BabyBear; WIDTH]) -> Vec<BabyBear>,
) -> ArmCount {
    let width = air.width;
    let mut values: Vec<P3BabyBear> = Vec::with_capacity(rows * width);
    for r in 0..rows {
        let input: [BabyBear; WIDTH] =
            core::array::from_fn(|i| BabyBear::new(((r * WIDTH + i) as u32) % 2_013_265_921));
        for v in fill(input) {
            values.push(to_p3(v));
        }
    }
    let trace = RowMajorMatrix::new(values, width);
    let ir2 = Ir2Air::lean_table(Arc::new(air.clone()));
    let config = counting_config();

    let instances = vec![StarkInstance::<CountingConfig, Ir2Air> {
        air: &ir2,
        trace: &trace,
        public_values: vec![],
    }];
    let prover_data = ProverData::from_instances(&config, &instances);

    PERMS.store(0, Ordering::Relaxed);
    let proof = prove_batch(&config, &instances, &prover_data);
    let prove_perms = PERMS.load(Ordering::Relaxed);

    let airs = [ir2.clone()];
    let pvs = vec![vec![]];
    PERMS.store(0, Ordering::Relaxed);
    verify_batch(&config, &airs, &proof, &pvs, &prover_data.common)
        .expect("an honest arm proof verifies");
    let verify_perms = PERMS.load(Ordering::Relaxed);

    ArmCount {
        cells: width * rows,
        prove_perms,
        verify_perms,
        bytes: json_len(&proof),
    }
}

/// ⚑ **THE PER-CHIP WIN, COUNTED** — both arms through the SAME `Ir2Air::LeanTable` interpreter, the
/// SAME FRI shape and the SAME row counts, so the only difference is the arithmetization.
///
/// ⚠ This is the PER-PERMUTATION figure and it is the FLATTERING one. What the deployed prover gets
/// is [`the_deployed_batch_committed_census`]'s number, which is much smaller because the chip is a
/// fraction of the batch. Quoting this one as "the prover" is the substitution that test exists to
/// prevent.
#[test]
#[ignore = "measurement; run with --run-ignored (release recommended)"]
fn the_two_arms_counted_at_the_deployed_fri_shape() {
    let w = wide_arm();
    let n = narrow_arm();
    println!("\n═══ PER-CHIP, COUNTED (lb={IR2_FRI_LOG_BLOWUP} q={IR2_FRI_NUM_QUERIES} pow=0) ═══");
    println!(
        "   committed lanes per permutation: wide {POSEIDON2_PERM_AUX_COLS}, narrow {POSEIDON2_PERM_AUX_COLS_NARROW}  ({:.4}×)",
        POSEIDON2_PERM_AUX_COLS as f64 / POSEIDON2_PERM_AUX_COLS_NARROW as f64
    );
    println!(
        "   standalone row width:            wide {WIDE_ARM_WIDTH}, narrow {NARROW_ARM_WIDTH}  ({:.4}×)",
        WIDE_ARM_WIDTH as f64 / NARROW_ARM_WIDTH as f64
    );
    println!(
        "\n   {:>6} {:>7} {:>10} {:>14} {:>14} {:>10}",
        "rows", "arm", "cells", "prove perms", "verify perms", "bytes"
    );
    for log_rows in [6usize, 8, 10] {
        let rows = 1usize << log_rows;
        let cw = count_arm(&w, rows, &wide_row);
        let cn = count_arm(&n, rows, &narrow_row);
        for (tag, c) in [("wide", &cw), ("narrow", &cn)] {
            println!(
                "   {rows:>6} {tag:>7} {:>10} {:>14} {:>14} {:>10}",
                c.cells, c.prove_perms, c.verify_perms, c.bytes
            );
        }
        println!(
            "   {rows:>6} {:>7} {:>9.4}× {:>13.4}× {:>13.4}× {:>9.4}×",
            "ratio",
            cw.cells as f64 / cn.cells as f64,
            cw.prove_perms as f64 / cn.prove_perms as f64,
            cw.verify_perms as f64 / cn.verify_perms as f64,
            cw.bytes as f64 / cn.bytes as f64,
        );
        assert!(
            cn.prove_perms < cw.prove_perms,
            "the narrow arm must cost strictly fewer prover permutations at {rows} rows"
        );
        assert!(
            cn.cells < cw.cells,
            "the narrow arm must commit strictly fewer cells at {rows} rows"
        );
    }
}

/// ⚑ **THE BATCH CENSUS** — the committed matrices of a REAL deployed descriptor batch, the exact
/// permutation count of its prove, and what the shape becomes when the chip's row loses 211 columns.
///
/// ⚠ **The narrow-chip line is ARITHMETIC ON MEASURED DIMS, not a measured prove.** The chip cannot
/// be cut over until `ChipTableEmit` re-emits at `CHIP_WIDTH = 175` (`Poseidon2RoundGates.lean`
/// §8g), and this file deliberately does not do that. What is measured: the batch's committed
/// shape, its total prover permutations, its proof bytes. What is derived: the cell and leaf-hash
/// totals under a 175-wide chip. The mechanism that carries committed width into prover work is the
/// Merkle LEAF sponge — `PaddingFreeSponge` over the whole committed row, `⌈w/8⌉` permutations per
/// row of the LDE — so the leaf column is the one the projection is about, and the LDE's common
/// `2^log_blowup` factor cancels out of every ratio below.
#[test]
#[ignore = "measurement; run with --run-ignored (release recommended)"]
fn the_deployed_batch_committed_census() {
    let state = CellState::new(100_000, 0);
    let effects = vec![Effect::Transfer {
        amount: 50,
        direction: 1,
    }];
    let (base_trace, pis) = generate_effect_vm_trace(&state, &effects);
    let json = descriptor2_for_key("transferVmDescriptor2").expect("the deployed transfer v2");
    let desc = parse_vm_descriptor2(json).expect("it parses");
    let dpis: Vec<BabyBear> = pis[..desc.public_input_count].to_vec();
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    let umem = UMemBoundaryWitness::default();
    let config = counting_config();

    PERMS.store(0, Ordering::Relaxed);
    let proof =
        prove_vm_descriptor2_for_config(&desc, &base_trace, &dpis, &mem, &heaps, &umem, &config)
            .expect("the deployed batch proves");
    let batch_perms = PERMS.load(Ordering::Relaxed);
    let bytes = json_len(&proof);

    PERMS.store(0, Ordering::Relaxed);
    verify_vm_descriptor2_with_config(&desc, &proof, &dpis, &config).expect("and verifies");
    let verify_perms = PERMS.load(Ordering::Relaxed);

    let (airs, _pvs, _common) = ir2_airs_and_common_for_config(&desc, &proof, &dpis, &config)
        .expect("the air set rebuilds");

    // The chip's deployed row and what it becomes: `CHIP_AUX0 (33) + aux + CHIP_MULT_NARROW (1)`.
    const CHIP_AUX0: usize = 33;
    const CHIP_WIDTH_WIDE: usize = CHIP_AUX0 + POSEIDON2_PERM_AUX_COLS + 1; // 386
    const CHIP_WIDTH_NARROW: usize = CHIP_AUX0 + POSEIDON2_PERM_AUX_COLS_NARROW + 1; // 175
    // ⚠ Identified by the emitted artifact's NAME, not by its width. A width is a display name in
    // this repo's own sense — two tables can share one — and a census that keyed on 386 would
    // silently re-scope the projection the day another table happened to be that wide.
    const CHIP_TABLES: [&str; 2] = ["dregg-ir2-chip-v1", "dregg-ir2-chip-state16-v1"];

    println!("\n═══ BATCH: the deployed transfer batch, COUNTED (pow=0) ═══");
    println!(
        "   prove {batch_perms} perms (incl. self-verify) · verify {verify_perms} perms · {bytes} bytes"
    );
    println!(
        "   {:>6} {:>8} {:>10} {:>12} {:>6} {:>6}  {}",
        "width", "height", "cells", "leaf perms", "permW", "quotW", "instance"
    );
    // ⚑ THE MAIN TRACES ARE NOT THE WHOLE COMMITTED SET. The prover commits three rounds: the main
    // traces, the per-instance LogUp PERMUTATION traces, and the QUOTIENT chunks. **Narrowing the
    // chip shrinks only the first.** Its bus interface is untouched (same tuples, same multiplicity
    // columns), so its permutation trace is the same width; its `max_constraint_degree` is
    // untouched at 7, so its quotient chunk count is the same. A census that stops at the main
    // traces therefore reports a batch factor that is an UPPER BOUND, and quoting it as the batch
    // figure would be quoting the flattering member of a pair again.
    //
    // Both extra rounds are read OFF THE PROOF, not modelled. The PCS opens a committed BASE-field
    // matrix and returns one `Challenge` per base column, so `permutation_local.len()` is the
    // permutation matrix's base width and `Σ quotient_chunks[c].len()` is the quotient's.
    //
    // ⚠ That reading is CHECKED, not assumed: `trace_local` is the same kind of opening over a
    // matrix whose width is independently known (the AIR's own `width()`), so if the convention
    // were "one opening per extension element" this assertion would fail by a factor of four
    // rather than silently re-scale every number below.
    for (i, air) in airs.iter().enumerate() {
        assert_eq!(
            proof.opened_values.instances[i]
                .base_opened_values
                .trace_local
                .len(),
            <Ir2Air as BaseAir<P3BabyBear>>::width(air),
            "instance {i}: an opening is not one value per BASE column, so the permutation and \
             quotient widths read below would be wrong by the extension degree"
        );
    }

    // (cells, leaf perms) accumulated per commitment round, wide arm and narrow projection.
    let mut round = [[(0usize, 0usize); 2]; 3]; // [main|perm|quotient][wide|narrow]
    let (mut chip_cells, mut chip_leaf, mut chips) = (0usize, 0usize, 0usize);
    let mut add = |r: usize, w: usize, nw: usize, h: usize| {
        round[r][0].0 += w * h;
        round[r][0].1 += w.div_ceil(8) * h;
        round[r][1].0 += nw * h;
        round[r][1].1 += nw.div_ceil(8) * h;
    };
    for (i, air) in airs.iter().enumerate() {
        let width = <Ir2Air as BaseAir<P3BabyBear>>::width(air);
        let height = 1usize << proof.degree_bits[i];
        let name = air
            .lean_table_air()
            .map_or_else(|| "main (descriptor)".to_string(), |t| t.name.clone());
        let is_chip = CHIP_TABLES.contains(&name.as_str());
        if is_chip {
            assert_eq!(
                width, CHIP_WIDTH_WIDE,
                "`{name}` is {width} wide, not the {CHIP_WIDTH_WIDE} this projection assumes"
            );
            chips += 1;
            chip_cells += width * height;
            chip_leaf += width.div_ceil(8) * height;
        }
        let nw = if is_chip { CHIP_WIDTH_NARROW } else { width };
        let ov = &proof.opened_values.instances[i];
        let perm_w = ov.permutation_local.len();
        let quot_w: usize = ov
            .base_opened_values
            .quotient_chunks
            .iter()
            .map(Vec::len)
            .sum();
        add(0, width, nw, height);
        add(1, perm_w, perm_w, height); // ← UNCHANGED by the narrowing
        add(2, quot_w, quot_w, height); // ← UNCHANGED by the narrowing
        println!(
            "   {width:>6} {height:>8} {:>10} {:>12} {perm_w:>6} {quot_w:>6}  {name}{}",
            width * height,
            width.div_ceil(8) * height,
            if is_chip { "   ← CHIP" } else { "" }
        );
    }
    assert!(
        chips > 0,
        "no chip table is present in this batch — the projection would be about nothing"
    );
    let names = ["main traces", "+ LogUp perm", "+ quotient"];
    let (mut cum_w, mut cum_n) = ((0usize, 0usize), (0usize, 0usize));
    println!(
        "\n   {:>14} {:>10} {:>12} {:>10} {:>12} {:>9} {:>9}",
        "committed set", "cells", "leaf perms", "narrow", "narrow leaf", "cell ×", "leaf ×"
    );
    for r in 0..3 {
        cum_w = (cum_w.0 + round[r][0].0, cum_w.1 + round[r][0].1);
        cum_n = (cum_n.0 + round[r][1].0, cum_n.1 + round[r][1].1);
        println!(
            "   {:>14} {:>10} {:>12} {:>10} {:>12} {:>8.4}× {:>8.4}×",
            names[r],
            cum_w.0,
            cum_w.1,
            cum_n.0,
            cum_n.1,
            cum_w.0 as f64 / cum_n.0 as f64,
            cum_w.1 as f64 / cum_n.1 as f64,
        );
    }
    println!(
        "\n   CHIP SHARE of the MAIN traces: cells {:.2}% · leaf perms {:.2}%",
        100.0 * chip_cells as f64 / round[0][0].0 as f64,
        100.0 * chip_leaf as f64 / round[0][0].1 as f64
    );
    println!(
        "   ⚑ PER-CHIP {:.4}× on the chip's own row  →  PER-BATCH {:.4}× over the WHOLE committed \
         set (main + LogUp + quotient).",
        CHIP_WIDTH_WIDE as f64 / CHIP_WIDTH_NARROW as f64,
        cum_w.1 as f64 / cum_n.1 as f64
    );
    println!(
        "   ⚠ and {:.4}× if you stop at the main traces, which is the flattering half.",
        round[0][0].1 as f64 / round[0][1].1 as f64
    );
}
