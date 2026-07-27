//! # THE KERNEL-STEP PROVE, ON THE GPU, ACROSS FRI PARAMETERIZATIONS.
//!
//! What this measures, and why it did not exist before.
//!
//! The recorded kernel-step number (`docs/MEASURE-legacy-1felt-chain-drop.md` §5,
//! ~637.9 ms) is a **CPU laptop** figure for the deployed rotated transfer leg at the
//! production `ir2_config` knobs (`log_blowup = 6, queries = 19, query_pow = 16`). The
//! only GPU leaf entry that existed (`prove_vm_descriptor2_gpu_zk`) drives the **hiding /
//! zk** config (`lb = 3, q = 38`), not the deployed one, and its single `#[ignore]`d
//! consumer has never had its output recorded anywhere in the tree. So "what does a turn
//! cost on the forge's GPU" had no answer at all.
//!
//! This closes that. The statement proven is the **deployed wide transfer leg**, minted
//! through the production dispatcher
//! (`generate_rotated_effect_vm_descriptor_and_trace_wide` — the exact call
//! `mint_rotated_participant_leg` makes), so descriptor / trace / PI vector / witnesses
//! are the deployed set, not a fixture.
//!
//! **The A/B is clean by construction.** `DreggRecursionConfig` and
//! `GpuDreggRecursionConfig` are built by twin `_with_fri` constructors that take the
//! same six knobs, share `default_babybear_poseidon2_16()`, share MMCS seed 0, and share
//! `Challenge = EF` (BabyBear ext degree 4). They differ in **exactly two things**: which
//! `TwoAdicSubgroupDft` runs the LDE, and which `Mmcs` builds the Merkle layers. Every
//! other byte of the prover is the same code. The byte-identity assertion below is what
//! makes that claim checkable rather than asserted.
//!
//! ⚑ **MEASURED FINDING — the deployed kernel step never dispatches a GPU DFT.** Every row
//! below reports `0 DFT dispatches` against 9-12 GPU Merkle commits. The whole GPU win here
//! is the **Merkle/hash offload**; the LDE runs on the CPU in both arms. Two independent
//! reasons, both confirmed on the box:
//!
//! 1. `GpuDft::coset_lde_batch` gates on `mat.height()` — the **input** height — while the
//!    work it does is the **output** height (`h << added_bits`) times the width. The
//!    deployed trace is 64 rows x 2726 columns at `log_blowup = 6`: an 11.2M-cell LDE,
//!    rejected as "64 < 4096" by `MIN_GPU_LOG_H`. Width is absent from the gate entirely.
//! 2. Correcting (1) does NOT work, and that is the real wall: gating on the output height
//!    makes the generator emit `fused1b_l6_two2048`, which fails to compile —
//!    `let g = reverseBits(c0 + b2) >> (32u - (6u - 8u));` underflows, because the kernel
//!    family assumes input log-height >= `E1` (8). So a 64-row input is not merely
//!    unprofitable, it is **unrepresentable** in the current shader generator.
//!
//! Putting the deployed turn's LDE on the GPU therefore needs a short-input kernel variant
//! (or padding the trace to 2^12 rows before the LDE and paying for the pad) — scoped work,
//! not a threshold constant. Until then the 5.7x below is a pure hash-offload number, and
//! the DFT term is headroom nobody has collected.
//!
//! ⚑ **What "reparameterized" can and cannot mean here.** The sweep moves
//! `(log_blowup, num_queries)`, which moves the *conjectured* figure `q·lb + pow` that the
//! field quotes. It CANNOT move the proven posture past the extension-degree-4 ceiling
//! (~78 bits; deployed reading 51 — `docs/reference/PROVEN-120-CONFIG.md`). A genuine
//! proven-120 needs `d = 8`, which is a Challenge-**type** change across every config, not
//! a knob this harness can turn. The `q = 36` row exists to price the query column that
//! the `d = 8` design would need, at the degree we actually ship.
//!
//! Run (release; debug prove times are lies), on the box with the AMD card:
//! ```text
//! scripts/hbuild gpu-e2e env DREGG_REQUIRE_WGPU=1 \
//!   cargo nextest run --release -p dregg-circuit-prove \
//!   --test gpu_kernel_step_reparam_measure --run-ignored all --no-capture
//! ```

use std::time::{Duration, Instant};

use dregg_circuit::CellState;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::Effect;
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, generate_rotated_effect_vm_descriptor_and_trace_wide,
    transfer_caveat_manifest,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit_prove::gpu_backend::{
    GpuDft, create_gpu_recursion_config_with_fri, hiding_gpu_dispatch_counters,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_config_with_fri,
};
use dregg_turn::rotation_witness as rw;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};

/// Timing reps per (config, arm). The recorded CPU baseline used best-of-3; matching it
/// keeps the two numbers comparable. The first GPU rep pays shader compilation, so
/// best-of-3 is also what makes the GPU arm honest rather than warm-up-dominated.
const REPS: usize = 3;

/// The production `ir2_config` shape, held fixed across the sweep so only `(lb, q)` move:
/// `log_final_poly_len = 0`, `max_log_arity = 3`, `commit_pow = 0`, `query_pow = 16`
/// (`circuit/src/descriptor_ir2.rs` — `IR2_FRI_*`).
const LOG_FINAL_POLY_LEN: usize = 0;
const MAX_LOG_ARITY: usize = 3;
const COMMIT_POW_BITS: usize = 0;
const QUERY_POW_BITS: usize = 16;

/// The recorded pre-existing CPU baseline for the deployed row, for the delta line only
/// (`docs/MEASURE-legacy-1felt-chain-drop.md` §5, M2 Max laptop).
const RECORDED_LAPTOP_CPU_MS: f64 = 637.9;

struct ParamPoint {
    label: &'static str,
    log_blowup: usize,
    num_queries: usize,
}

/// The sweep. `conjectured = q·lb + query_pow` is the figure the field quotes; it is NOT a
/// proven bound and this harness does not pretend otherwise (see the module header).
const SWEEP: &[ParamPoint] = &[
    ParamPoint {
        label: "conj-100 @ lb6",
        log_blowup: 6,
        num_queries: 14,
    },
    ParamPoint {
        label: "DEPLOYED conj-130",
        log_blowup: 6,
        num_queries: 19,
    },
    ParamPoint {
        label: "conj-100 @ lb3",
        log_blowup: 3,
        num_queries: 28,
    },
    ParamPoint {
        label: "q36 (d8-proven120 query column)",
        log_blowup: 6,
        num_queries: 36,
    },
];

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// The honest wide transfer, minted through the PRODUCTION dispatcher — byte-for-byte the
/// fixture the recorded CPU baseline used (`circuit/tests/legacy_chain_drop_measurement.rs`),
/// so the two measurements are of the same statement.
fn honest_wide_transfer() -> (
    EffectVmDescriptor2,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
    Vec<Vec<HeapLeaf>>,
    MemBoundaryWitness,
) {
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance);
    let after_cell = producer_cell(before_balance - amount as i64);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let produce = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let bridge =
        |w: &rw::RotationWitness| RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).unwrap();
    let before_w = produce(&before_cell);
    let after_w = produce(&after_cell);
    let membership_teeth = (BabyBear::new(0xA11CE), BabyBear::new(0xF00D));
    let (desc, trace, dpis, map_heaps, mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
        None,
        None,
        None,
        Some(membership_teeth),
    )
    .expect("the deployed wide transfer leg mints");
    (desc, trace, dpis, map_heaps, mb)
}

fn best_median_max(mut samples: Vec<Duration>) -> (f64, f64, f64) {
    samples.sort();
    (
        samples[0].as_secs_f64() * 1e3,
        samples[samples.len() / 2].as_secs_f64() * 1e3,
        samples[samples.len() - 1].as_secs_f64() * 1e3,
    )
}

#[test]
#[ignore = "GPU + proof-heavy: run on hbox with DREGG_REQUIRE_WGPU=1 and --run-ignored all"]
fn deployed_kernel_step_cpu_vs_gpu_across_fri_parameterizations() {
    assert_eq!(
        std::env::var("DREGG_REQUIRE_WGPU").as_deref(),
        Ok("1"),
        "this measurement is meaningful only in the hard DREGG_REQUIRE_WGPU=1 posture — \
         otherwise a silent all-CPU fallback would be reported as a GPU number"
    );
    let adapter = GpuDft::default()
        .adapter_name()
        .expect("this measurement requires a named portable GPU adapter");

    let (desc, trace, dpis, map_heaps, mb) = honest_wide_transfer();
    let umem = UMemBoundaryWitness::default();

    eprintln!("\n=== DEPLOYED KERNEL STEP — CPU vs GPU across FRI parameterizations ===");
    eprintln!("adapter: {adapter}");
    eprintln!(
        "statement: deployed wide transfer leg, {} base trace rows, {} PIs, {} reps/arm",
        trace.len(),
        dpis.len(),
        REPS
    );
    eprintln!(
        "fixed: log_final_poly_len={LOG_FINAL_POLY_LEN}, max_log_arity={MAX_LOG_ARITY}, \
         commit_pow={COMMIT_POW_BITS}, query_pow={QUERY_POW_BITS}, ext degree 4"
    );
    eprintln!(
        "\n{:<34} {:>4} {:>4} {:>6} {:>11} {:>11} {:>8} {:>11}",
        "config", "lb", "q", "conj", "CPU best ms", "GPU best ms", "ratio", "proof B"
    );

    for point in SWEEP {
        let conjectured = point.num_queries * point.log_blowup + QUERY_POW_BITS;

        let cpu_config: DreggRecursionConfig = create_recursion_config_with_fri(
            point.log_blowup,
            LOG_FINAL_POLY_LEN,
            MAX_LOG_ARITY,
            point.num_queries,
            COMMIT_POW_BITS,
            QUERY_POW_BITS,
        );
        let gpu_config = create_gpu_recursion_config_with_fri(
            point.log_blowup,
            LOG_FINAL_POLY_LEN,
            MAX_LOG_ARITY,
            point.num_queries,
            COMMIT_POW_BITS,
            QUERY_POW_BITS,
        );

        // ---- CPU arm ----
        let mut cpu_samples = Vec::with_capacity(REPS);
        let mut cpu_bytes = Vec::new();
        for _ in 0..REPS {
            let started = Instant::now();
            let proof = prove_vm_descriptor2_for_config(
                &desc,
                &trace,
                &dpis,
                &mb,
                &map_heaps,
                &umem,
                &cpu_config,
            )
            .unwrap_or_else(|e| panic!("[{}] CPU prove failed: {e}", point.label));
            cpu_samples.push(started.elapsed());
            cpu_bytes = postcard::to_allocvec(&proof).expect("CPU proof serializes");
        }

        // ---- GPU arm ----
        let before = hiding_gpu_dispatch_counters();
        let mut gpu_samples = Vec::with_capacity(REPS);
        let mut gpu_bytes = Vec::new();
        for _ in 0..REPS {
            let started = Instant::now();
            let proof = prove_vm_descriptor2_for_config(
                &desc,
                &trace,
                &dpis,
                &mb,
                &map_heaps,
                &umem,
                &gpu_config,
            )
            .unwrap_or_else(|e| panic!("[{}] GPU prove failed: {e}", point.label));
            gpu_samples.push(started.elapsed());
            gpu_bytes = postcard::to_allocvec(&proof).expect("GPU proof serializes");
        }
        // ⚑ `require_hiding_gpu_dispatch_since` is the WRONG gate for this config and the
        // first run of this harness proved it: it demands a **HidingFRI matrix fold**, a
        // counter only the `HidingFriPcs` path increments. `GpuFoldPcs` is a plain
        // `TwoAdicFriPcs`, so that counter is structurally zero here and the gate fired on a
        // proof that had in fact run on the GPU. The evidence this config CAN produce is the
        // DFT dispatch and the BabyBear Merkle commit; both must move, or the row is an
        // all-CPU number wearing a GPU label.
        let after = hiding_gpu_dispatch_counters();
        let dft_delta = after.dft_dispatches - before.dft_dispatches;
        let commit_delta = after.babybear_merkle_commits - before.babybear_merkle_commits;
        // The gate that must bite: SOME GPU work has to have happened, or the row is an
        // all-CPU number wearing a GPU label. The DFT count is REPORTED, not gated —
        // measuring it is the point (see the `MIN_GPU_LOG_H` note in the module header).
        assert!(
            commit_delta > 0,
            "[{}] the GPU arm did NO GPU work at all: {dft_delta} DFT, {commit_delta} \
             Merkle commits over {REPS} proves",
            point.label
        );

        // The two arms differ ONLY in DFT + MMCS implementation, so the wire must agree
        // byte-for-byte. If this ever goes red it is a real backend divergence, not a
        // measurement artifact — do not soften it into a warning.
        assert_eq!(
            cpu_bytes,
            gpu_bytes,
            "[{}] CPU and GPU proofs diverged ({} vs {} bytes) — the GPU backend is not \
             bit-exact at this parameterization",
            point.label,
            cpu_bytes.len(),
            gpu_bytes.len()
        );

        // And the untouched CPU verifier must accept the GPU-produced receipt.
        let (retagged, remainder): (Ir2BatchProof<DreggRecursionConfig>, &[u8]) =
            postcard::take_from_bytes(&gpu_bytes).expect("GPU proof re-tags into the CPU type");
        assert!(
            remainder.is_empty(),
            "[{}] GPU proof re-tag left {} trailing bytes",
            point.label,
            remainder.len()
        );
        verify_vm_descriptor2_with_config(&desc, &retagged, &dpis, &cpu_config).unwrap_or_else(
            |e| {
                panic!(
                    "[{}] CPU verifier rejected the GPU receipt: {e:?}",
                    point.label
                )
            },
        );

        let (cpu_best, cpu_med, cpu_max) = best_median_max(cpu_samples);
        let (gpu_best, gpu_med, gpu_max) = best_median_max(gpu_samples);

        eprintln!(
            "{:<34} {:>4} {:>4} {:>6} {:>11.1} {:>11.1} {:>7.2}x {:>11}",
            point.label,
            point.log_blowup,
            point.num_queries,
            conjectured,
            cpu_best,
            gpu_best,
            cpu_best / gpu_best,
            cpu_bytes.len()
        );
        eprintln!(
            "    CPU best/med/max {cpu_best:.1}/{cpu_med:.1}/{cpu_max:.1} ms | \
             GPU best/med/max {gpu_best:.1}/{gpu_med:.1}/{gpu_max:.1} ms | \
             GPU dispatches over {REPS} proves: {dft_delta} DFT, {commit_delta} Merkle commits"
        );
    }

    eprintln!(
        "\nrecorded laptop-CPU baseline for the DEPLOYED row (M2 Max, \
         docs/MEASURE-legacy-1felt-chain-drop.md §5): {RECORDED_LAPTOP_CPU_MS:.1} ms \
         — a DIFFERENT machine and a different config wrapper; read it as provenance, \
         not as this table's CPU column."
    );
    eprintln!(
        "PROVEN posture is NOT what the `conj` column reports: at ext degree 4 the ceiling \
         is ~78 bits and the deployed reading is 51 (docs/reference/PROVEN-120-CONFIG.md). \
         No row here is a 100-bit PROVEN configuration; none can be.\n"
    );
}
