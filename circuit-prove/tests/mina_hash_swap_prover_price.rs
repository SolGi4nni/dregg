//! ⚑ **THE DREGG-SIDE PRICE OF A MINA-NATIVE COMMITMENT — measured, not modelled.**
//!
//! The Mina-facing walk got 9.8× cheaper by hashing dregg's root proof with
//! **Mina-Poseidon over Pasta Fp** instead of **Poseidon2 over BabyBear**
//! (`GOAL-MINA-SEMANTIC-LIGHTCLIENTS.md`, 10:15). That measurement re-hashes
//! dregg's committed digests in TypeScript; a real deployment needs
//! [`dregg_circuit_prove::dregg_mina_config::DreggMinaConfig`] wired into the
//! **root prover**, i.e. dregg minting the root with a Pasta hash. Nobody had
//! priced that side. This file does.
//!
//! ## ⚑ SUBSTRATE (HOUSE LAW #1)
//!
//! **No AIR, no constraint, no gadget, no `air_accepts` in this file, and no
//! toy AIR either.** It never calls `prove`; it drives the `Pcs` trait
//! directly — `commit_ldes` (Merkle hashing), `commit` (LDE + Merkle) and
//! `open` (DEEP reduction + FRI commit phase + query openings + grinding).
//! That is the whole of what a hash-field swap can touch, and it is *prover
//! plumbing*. The AIRs remain Lean-authored and are not involved: this
//! measurement is deliberately AIR-free precisely so that no Rust constraint
//! content has to exist for it to run.
//!
//! ## Why the `Pcs` layer is the right instrument, not a shortcut
//!
//! `Val = BabyBear` and `Challenge = EF4` are identical across all three
//! configs, so trace generation, the LDE/DFT, the quotient evaluation and the
//! DEEP reduction are **byte-identical work**. The only thing that differs is
//! which prime field the Merkle/transcript hash runs in. Therefore the delta
//! between two configs' `commit`+`open` times *is* the hashing delta, with no
//! modelling step in between — and `commit` vs `commit_ldes` splits the LDE
//! (shared) from the Merkle (not shared) as a control.
//!
//! ## The geometry is the REAL root's, read off the committed object
//!
//! `bridge/mina-zkapp/.fullchain/real-root-fri.json` is the emitted FRI
//! instance of the deployed whole-history root proof
//! (`ugc-dregg/tests/fixtures/whole_history_proof.bin`). Its four committed
//! rounds, seven instances, per-matrix widths, per-instance degree bits and FRI
//! knobs are transcribed into the consts below. `log_global_max_height = 22`.
//!
//! ## Running it
//!
//! Every measurement is `#[ignore]`d and takes minutes to tens of minutes.
//! `HASH_SWAP_SHRINK=k` shifts every instance's degree bits down by `k`, which
//! is how the scaling exponent is obtained (the FRI knobs are held fixed).
//!
//! ```text
//! cargo test -p dregg-circuit-prove --release --test mina_hash_swap_prover_price -- --ignored --nocapture
//! HASH_SWAP_SHRINK=4 cargo test ... -- --ignored --nocapture merkle_commit
//! ```
//!
//! For peak RSS, run one test per process under `/usr/bin/time -l`.
//!
//! ## ⛑ MEASURED 2026-07-31 — one box, one process at a time, `--release`
//!
//! Apple aarch64, 12 cores, 96 GB. **Every figure below is SINGLE-THREADED and
//! that is not a choice of this harness**: `p3-maybe-rayon` resolves in this
//! workspace with **zero features** (`cargo metadata` on the whole resolve), so
//! the `parallel` feature is off and every `par_*` call in `p3-merkle-tree`,
//! `p3-dft`, `p3-fri` and `p3-uni-stark` is the serial fallback. `user ≈ real`
//! on every run confirms it (4,585 user / 5,149 real on the full-geometry run).
//! Three sketch crates outside the workspace (`circuit-prove/sketches/*-ntt`)
//! turn it on for `p3-dft`; the shipping tree turns it on nowhere.
//!
//! ### ⛑⛑ THE HEADLINE — the real root, all 1,734,899,840 committed LDE cells
//!
//! | commitment hash | `commit_ldes`, four rounds | per cell | vs deployed |
//! |---|---:|---:|---:|
//! | Poseidon2-BabyBear-W16 (**deployed root**) | **43.23 s** | 24.92 ns | 1x |
//! | Poseidon2-BN254 (ETH terminal) | **1,494.64 s** (24.9 min) | 861.51 ns | 34.6x |
//! | **Mina-Poseidon / Pasta** (`DreggMinaConfig`) | **3,608.76 s** (60.1 min) | 2,080.10 ns | **83.5x** |
//!
//! Per round, Pasta: main 1,474.2 s . quotient 267.7 s . preprocessed 1,019.3 s
//! . permutation 847.6 s. Peak RSS **5.59 GB** (all three legs, one process).
//!
//! ### [2] the scaling sweep, and ⚠ THE SHAPE IS NOT WHAT LINEARITY PREDICTS
//!
//! | LDE cells | BabyBear | BN254 | Pasta | Pasta ns/cell |
//! |---:|---:|---:|---:|---:|
//! | 6.83 M | 0.17 s | 6.18 s | 12.76 s | 1,869.1 |
//! | 27.15 M | 0.70 s | 21.64 s | 47.41 s | 1,745.9 |
//! | 108.46 M | 2.70 s | 85.55 s | 188.81 s | 1,740.8 |
//! | **1,734.90 M** | **43.23 s** | **1,494.64 s** | **3,608.76 s** | **2,080.1** |
//!
//! log-log exponents, last octave (108 M -> 1,735 M) and least-squares over all
//! four points:
//!
//! | | last octave | all four | naive-linear extrapolation from 108 M |
//! |---|---:|---:|---|
//! | BabyBear | **1.0004** | 0.998 | under by **0.1%** |
//! | BN254 | 1.0318 | 0.996 | under by **8.4%** |
//! | Pasta | **1.0642** | 1.023 | under by **16.3%** |
//!
//! ⛑ **The deployed 31-bit hash is exactly linear in committed cells. The wide
//! hashes are NOT** — they turn over into mild superlinearity at scale, and the
//! wider the field the sooner. Extrapolating the Pasta root linearly from the
//! largest affordable sub-scale point predicts 3,020 s against a measured
//! 3,609 s. **That is why the 1,735 M point is measured here and not modelled**,
//! and any future re-price of a bigger batch must measure rather than scale.
//! The mechanism is not settled by this harness (the Pasta leg streams a ~5.6 GB
//! working set on one core; cache/TLB behaviour is the obvious suspect and is
//! NOT verified) — the exponent is the measurement, the cause is not.
//!
//! ### [1] permutation microbench (single thread, 200,000 iterations)
//!
//! | permutation | ns/perm | BabyBear lanes/perm | ns/lane |
//! |---|---:|---:|---:|
//! | `Poseidon2BabyBear<16>` (deployed root) | 811.6 | 8 | **101.5** |
//! | `Poseidon2Bn254<3>` (ETH terminal) | 8,718.8 | 16 | **544.9** |
//! | `MinaPoseidonPerm` (Mina terminal) | 20,472.4 | 16 | **1,279.5** |
//!
//! ⚠ **An earlier run of this same bench read 1,343 / 22,843 / 34,545 ns/perm
//! — 1.7-2.6x slower — and it was wrong.** A sibling lane was building on this
//! shared tree at the time. The figures above are the re-run on a quiet box
//! immediately after the full-geometry measurement. The tell that something was
//! off was a *physical impossibility*: the contaminated bench put the per-lane
//! floor at 2,159 ns while the tree measured 1,740 ns/cell, and a leaf sponge
//! absorbing <=16 lanes per permutation, plus compressions on top, cannot come
//! in under its own permutation cost. With the clean numbers the check closes
//! the right way — the tree pays **1.63x** the ideal 1,279.5 ns/lane (imperfect
//! sponge fill on narrow matrices, plus the 2:1 compressions).
//! **Quote [2]; [1] is a unit price only.**
//!
//! ### [3] the LDE control — it came back IMPOSSIBLE, and that is the result
//!
//! At `SHRINK=4`, `commit` minus `commit_ldes` implies an LDE of **0.22 s
//! (BabyBear), 4.33 s (BN254), -3.26 s (Pasta)**. A negative LDE cannot happen,
//! so the spread is this method's noise floor: **+/-~3.5 s on a 100-200 s
//! quantity, i.e. +/-2%**. What survives is the bound it was built to give — the
//! coset LDE at blowup 64 is under 2% of the Pasta commit and is therefore not
//! where the delta lands. **Do not quote the BabyBear 0.22 s as an LDE
//! measurement**; quote the bound.
//!
//! ### [4] `commit_ldes` + `open` at `SHRINK=4` — the phase attribution
//!
//! | | Merkle (4 input rounds) | `open` (DEEP + FRI commit phase + queries + PoW) | opening proof |
//! |---|---:|---:|---:|
//! | BabyBear | 3.03 s | 0.28 s | 293,767 B |
//! | BN254 | 87.87 s | 7.01 s | 270,026 B |
//! | Pasta | 189.91 s | 11.75 s | 270,118 B |
//!
//! **94.2% of the Pasta-minus-BabyBear delta is the input-round MMCS commit**;
//! 5.8% is everything `open` does. Proof size **falls** 0.919x.
//!
//! ### The buckets, named — and what is NOT in them
//!
//! IN: (B1) input-round Merkle hashing, (B2) coset LDE, (B3) `open`.
//! OUT: trace generation, quotient-polynomial evaluation, AIR symbolic setup,
//! verification. Those are BabyBear-only work, identical under all three
//! configs, so they are absent from every DELTA quoted here and present in a
//! real prove — every "share" above is a share of B1+B2+B3, never of a whole
//! prove.

use std::time::{Duration, Instant};

use dregg_circuit_prove::dregg_mina_config::create_mina_config_with_fri;
use dregg_circuit_prove::dregg_outer_config::create_outer_config_with_fri;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::create_recursion_config_with_fri;
use p3_baby_bear::BabyBear;
use p3_commit::Pcs;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::extension::BinomialExtensionField;
use p3_field::integers::QuotientMap;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_symmetric::Permutation;
use p3_uni_stark::StarkGenericConfig;
use rayon::prelude::*;

type EF = BinomialExtensionField<BabyBear, 4>;

// ============================================================================
// The REAL root's committed geometry (real-root-fri.json)
// ============================================================================

/// `knobs.logBlowup` of the deployed root proof.
const ROOT_LOG_BLOWUP: usize = 6;
/// `knobs.numQueries`.
const ROOT_NUM_QUERIES: usize = 19;
/// `knobs.queryPowBits`.
const ROOT_QUERY_POW_BITS: usize = 16;
/// `knobs.maxLogArity` (fold by 2).
const ROOT_MAX_LOG_ARITY: usize = 1;
/// `knobs.logFinalPolyLen` (constant final poly).
const ROOT_LOG_FINAL_POLY_LEN: usize = 0;
/// `knobs.commitPowBits`.
const ROOT_COMMIT_POW_BITS: usize = 0;

/// `degreeBits` — one per instance, in `tables` order:
/// `Const, Public, Alu, poseidon2_perm/bb_d4_w16, poseidon2_perm/bb_d4_w24, recompose, expose_claim`.
const ROOT_DEGREE_BITS: [usize; 7] = [10, 10, 16, 15, 3, 16, 0];
/// Round 0 (`main`) widths.
const W_MAIN: [usize; 7] = [4, 4, 76, 300, 452, 4, 100];
/// Round 2 (`preprocessed`) widths.
const W_PREP: [usize; 7] = [2, 2, 59, 24, 36, 2, 50];
/// Round 3 (`permutation`) widths — EF4 columns already flattened to base lanes.
const W_PERM: [usize; 7] = [4, 4, 72, 28, 44, 4, 100];
/// Round 1 (`quotient_chunk`): two chunks per instance, four base lanes each.
const QUOTIENT_CHUNKS: usize = 2;
const W_QUOT: usize = 4;

/// Opening-point counts per matrix, per round, as the emitted instance records
/// them (`points` array lengths): the wide tables open at `{zeta, zeta*g}`, the
/// rest at `{zeta}`; the whole permutation round opens at two points.
const P_MAIN: [usize; 7] = [1, 1, 2, 2, 2, 1, 1];
const P_PREP: [usize; 7] = [1, 1, 2, 2, 2, 1, 1];
const P_PERM: [usize; 7] = [2, 2, 2, 2, 2, 2, 2];

/// One committed round: `(log_lde_height, width, num_opening_points)` per matrix.
type Round = Vec<(usize, usize, usize)>;

/// The four committed rounds at `shrink` fewer degree bits per instance.
/// `shrink = 0` is the deployed root exactly.
fn root_rounds(shrink: usize) -> Vec<Round> {
    let log_h = |i: usize| ROOT_DEGREE_BITS[i].saturating_sub(shrink) + ROOT_LOG_BLOWUP;

    let main: Round = (0..7).map(|i| (log_h(i), W_MAIN[i], P_MAIN[i])).collect();
    let mut quot: Round = Vec::new();
    for i in 0..7 {
        for _ in 0..QUOTIENT_CHUNKS {
            quot.push((log_h(i), W_QUOT, 1));
        }
    }
    let prep: Round = (0..7).map(|i| (log_h(i), W_PREP[i], P_PREP[i])).collect();
    let perm: Round = (0..7).map(|i| (log_h(i), W_PERM[i], P_PERM[i])).collect();
    vec![main, quot, prep, perm]
}

fn shrink_from_env() -> usize {
    std::env::var("HASH_SWAP_SHRINK")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0)
}

fn cells(rounds: &[Round]) -> u64 {
    rounds
        .iter()
        .flat_map(|r| r.iter())
        .map(|&(lh, w, _)| (1u64 << lh) * w as u64)
        .sum()
}

/// Deterministic filler. The hash cost does not depend on the values; only on
/// how many there are and whether they are canonical BabyBear.
fn matrix(log_h: usize, w: usize, seed: u64) -> RowMajorMatrix<BabyBear> {
    const P: u32 = 0x7800_0001;
    let h = 1usize << log_h;
    let mut values: Vec<BabyBear> = vec![BabyBear::ZERO; h * w];
    values
        .par_chunks_mut(1 << 16)
        .enumerate()
        .for_each(|(chunk, slot)| {
            let mut x = seed
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add(chunk as u64)
                | 1;
            for v in slot.iter_mut() {
                x = x
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                *v = BabyBear::from_int(((x >> 33) as u32) % P);
            }
        });
    RowMajorMatrix::new(values, w)
}

fn build_round(round: &Round, seed: u64) -> Vec<RowMajorMatrix<BabyBear>> {
    round
        .iter()
        .enumerate()
        .map(|(i, &(lh, w, _))| matrix(lh, w, seed ^ (i as u64) << 32))
        .collect()
}

// ============================================================================
// The three configs, at ONE knob set — the deployed root's
// ============================================================================

/// The knob set every config is instantiated at, so the ONLY difference
/// between them is the hash field. These are the deployed root's own knobs.
macro_rules! at_root_knobs {
    ($ctor:path) => {
        $ctor(
            ROOT_LOG_BLOWUP,
            ROOT_LOG_FINAL_POLY_LEN,
            ROOT_MAX_LOG_ARITY,
            ROOT_NUM_QUERIES,
            ROOT_COMMIT_POW_BITS,
            ROOT_QUERY_POW_BITS,
        )
    };
}

// ============================================================================
// The measurements, generic over the config (so one body, three hashes)
// ============================================================================

#[derive(Debug, Clone, Copy, Default)]
struct Split {
    /// `commit_ldes` — Merkle hashing of already-LDE'd matrices. Pure hashing.
    merkle: Duration,
    /// `open` — DEEP reduction + FRI commit phase (fold + per-layer Merkle
    /// commit) + query openings + query-PoW grinding.
    open: Duration,
    /// postcard bytes of the opening proof.
    proof_bytes: usize,
}

/// Merkle-hash-only: `commit_ldes` over the LDE-shaped matrices, one round at
/// a time so peak memory is one round rather than four.
fn merkle_only<SC>(config: &SC, rounds: &[Round]) -> Vec<Duration>
where
    SC: StarkGenericConfig<Challenge = EF>,
    SC::Pcs: Pcs<EF, SC::Challenger, Domain = TwoAdicMultiplicativeCoset<BabyBear>>,
{
    let pcs = config.pcs();
    let mut out = Vec::new();
    for (r, round) in rounds.iter().enumerate() {
        let mats = build_round(round, 0xC0FFEE ^ r as u64);
        let t = Instant::now();
        let (_c, data) = <SC::Pcs as Pcs<EF, SC::Challenger>>::commit_ldes(pcs, mats);
        let dt = t.elapsed();
        drop(data);
        out.push(dt);
    }
    out
}

/// LDE + Merkle: `commit` at the *base* domain shapes, so the PCS performs the
/// blowup-64 coset LDE itself. Subtracting [`merkle_only`] leaves the LDE,
/// which is config-independent by construction — running it under all three is
/// the control that says so.
fn commit_full<SC>(config: &SC, rounds: &[Round]) -> Vec<Duration>
where
    SC: StarkGenericConfig<Challenge = EF>,
    SC::Pcs: Pcs<EF, SC::Challenger, Domain = TwoAdicMultiplicativeCoset<BabyBear>>,
{
    let pcs = config.pcs();
    let mut out = Vec::new();
    for (r, round) in rounds.iter().enumerate() {
        let evals: Vec<_> = round
            .iter()
            .enumerate()
            .map(|(i, &(lh, w, _))| {
                let base_log_h = lh - ROOT_LOG_BLOWUP;
                let domain = <SC::Pcs as Pcs<EF, SC::Challenger>>::natural_domain_for_degree(
                    pcs,
                    1 << base_log_h,
                );
                (
                    domain,
                    matrix(base_log_h, w, 0xBEEF ^ (r as u64) << 40 ^ (i as u64) << 32),
                )
            })
            .collect();
        let t = Instant::now();
        let (_c, data) = <SC::Pcs as Pcs<EF, SC::Challenger>>::commit(pcs, evals);
        let dt = t.elapsed();
        drop(data);
        out.push(dt);
    }
    out
}

/// The whole opening argument over all four rounds at once.
fn commit_and_open<SC>(config: &SC, rounds: &[Round]) -> Split
where
    SC: StarkGenericConfig<Challenge = EF>,
    SC::Pcs: Pcs<EF, SC::Challenger, Domain = TwoAdicMultiplicativeCoset<BabyBear>>,
{
    let pcs = config.pcs();
    let mut datas = Vec::new();
    let mut merkle = Duration::ZERO;
    for (r, round) in rounds.iter().enumerate() {
        let mats = build_round(round, 0xC0FFEE ^ r as u64);
        let t = Instant::now();
        let (_c, data) = <SC::Pcs as Pcs<EF, SC::Challenger>>::commit_ldes(pcs, mats);
        merkle += t.elapsed();
        datas.push(data);
    }

    // Opening points: one shared `zeta` and its `zeta * g` shift, exactly the
    // two-point pattern the emitted instance records. Values are irrelevant to
    // cost; they must simply lie outside the evaluation domain, which a random
    // EF4 element does with overwhelming probability.
    let zeta = EF::GENERATOR * EF::from(BabyBear::from_int(0x1234_5678u32)) + EF::ONE;
    let zeta_next = zeta * EF::from(BabyBear::from_int(31u32));

    let args: Vec<_> = rounds
        .iter()
        .zip(datas.iter())
        .map(|(round, data)| {
            let pts: Vec<Vec<EF>> = round
                .iter()
                .map(|&(_, _, np)| {
                    if np >= 2 {
                        vec![zeta, zeta_next]
                    } else {
                        vec![zeta]
                    }
                })
                .collect();
            (data, pts)
        })
        .collect();

    let mut challenger = config.initialise_challenger();
    let t = Instant::now();
    let (_opened, proof) = <SC::Pcs as Pcs<EF, SC::Challenger>>::open(pcs, args, &mut challenger);
    let open = t.elapsed();
    let proof_bytes = postcard::to_allocvec(&proof)
        .expect("opening proof serializes")
        .len();

    Split {
        merkle,
        open,
        proof_bytes,
    }
}

fn secs(d: Duration) -> f64 {
    d.as_secs_f64()
}

fn total(v: &[Duration]) -> Duration {
    v.iter().copied().sum()
}

// ============================================================================
// [1] The permutation microbench — the primitive under everything else
// ============================================================================

#[test]
#[ignore = "MEASUREMENT: ~1 min. The three permutations' raw throughput."]
fn hash_swap_permutation_microbench() {
    use p3_baby_bear::{Poseidon2BabyBear, default_babybear_poseidon2_16};
    use p3_bn254::Bn254;
    use p3_pasta::{MinaPoseidonPerm, PastaFp};

    const N: usize = 200_000;

    // Poseidon2-BabyBear W16 — the DEPLOYED hash. Rate 8 BabyBear lanes.
    let bb: Poseidon2BabyBear<16> = default_babybear_poseidon2_16();
    let mut s = [BabyBear::ONE; 16];
    let t = Instant::now();
    for _ in 0..N {
        bb.permute_mut(&mut s);
    }
    let bb_ns = t.elapsed().as_secs_f64() * 1e9 / N as f64;
    let _ = core::hint::black_box(s);

    // Poseidon2-BN254 t=3 — the ETH terminal. Rate 2 BN254 = 16 BabyBear lanes.
    let bn = dregg_circuit_prove::dregg_outer_config::dregg_poseidon2_bn254();
    let mut s = [Bn254::ONE; 3];
    let t = Instant::now();
    for _ in 0..N {
        bn.permute_mut(&mut s);
    }
    let bn_ns = t.elapsed().as_secs_f64() * 1e9 / N as f64;
    let _ = core::hint::black_box(s);

    // Mina-Poseidon t=3, 55 FULL rounds, alpha=7 — the Mina terminal.
    let mp = MinaPoseidonPerm;
    let mut s = [PastaFp::ONE; 3];
    let t = Instant::now();
    for _ in 0..N {
        mp.permute_mut(&mut s);
    }
    let mp_ns = t.elapsed().as_secs_f64() * 1e9 / N as f64;
    let _ = core::hint::black_box(s);

    println!("=== [1] PERMUTATION MICROBENCH (single thread, {N} iterations) ===");
    println!(
        "Poseidon2-BabyBear<16>  {bb_ns:9.1} ns/perm   rate  8 BabyBear lanes  -> {:7.2} ns/lane",
        bb_ns / 8.0
    );
    println!(
        "Poseidon2-BN254<3>      {bn_ns:9.1} ns/perm   rate 16 BabyBear lanes  -> {:7.2} ns/lane",
        bn_ns / 16.0
    );
    println!(
        "Mina-Poseidon<3>        {mp_ns:9.1} ns/perm   rate 16 BabyBear lanes  -> {:7.2} ns/lane",
        mp_ns / 16.0
    );
    println!(
        "per-lane  Mina / BabyBear : {:.2}x",
        (mp_ns / 16.0) / (bb_ns / 8.0)
    );
    println!("per-lane  Mina / BN254    : {:.2}x", mp_ns / bn_ns);
    println!(
        "per-node (2:1 compress)  Mina / BabyBear : {:.2}x",
        mp_ns / bb_ns
    );
}

// ============================================================================
// [2] Merkle-commit price at the real root's geometry
// ============================================================================

#[test]
#[ignore = "MEASUREMENT: minutes to ~1h at HASH_SWAP_SHRINK=0. Commitment hashing, three hashes, real root geometry."]
fn hash_swap_merkle_commit_at_root_geometry() {
    let shrink = shrink_from_env();
    let rounds = root_rounds(shrink);
    let n_cells = cells(&rounds);
    println!("=== [2] MERKLE COMMIT (commit_ldes) — HASH_SWAP_SHRINK={shrink} ===");
    println!(
        "committed LDE cells: {n_cells} ({:.1} M)",
        n_cells as f64 / 1e6
    );
    for (i, r) in rounds.iter().enumerate() {
        let c: u64 = r.iter().map(|&(lh, w, _)| (1u64 << lh) * w as u64).sum();
        println!(
            "  round {i}: {:2} matrices, max logHeight {:2}, {:.1} M cells",
            r.len(),
            r.iter().map(|&(lh, _, _)| lh).max().unwrap(),
            c as f64 / 1e6
        );
    }

    let bb = at_root_knobs!(create_recursion_config_with_fri);
    let t_bb = merkle_only(&bb, &rounds);
    println!(
        "Poseidon2-BabyBear : {:8.2} s   {:?}",
        secs(total(&t_bb)),
        t_bb
    );
    drop(bb);

    let bn = at_root_knobs!(create_outer_config_with_fri);
    let t_bn = merkle_only(&bn, &rounds);
    println!(
        "Poseidon2-BN254    : {:8.2} s   {:?}",
        secs(total(&t_bn)),
        t_bn
    );
    drop(bn);

    let mn = at_root_knobs!(create_mina_config_with_fri);
    let t_mn = merkle_only(&mn, &rounds);
    println!(
        "Mina-Poseidon/Pasta: {:8.2} s   {:?}",
        secs(total(&t_mn)),
        t_mn
    );

    println!("--- ratios ---");
    println!(
        "Pasta / BabyBear : {:.2}x",
        secs(total(&t_mn)) / secs(total(&t_bb))
    );
    println!(
        "Pasta / BN254    : {:.2}x",
        secs(total(&t_mn)) / secs(total(&t_bn))
    );
    println!(
        "BN254 / BabyBear : {:.2}x",
        secs(total(&t_bn)) / secs(total(&t_bb))
    );
    println!("--- ns per committed cell ---");
    println!(
        "BabyBear {:7.2}  BN254 {:7.2}  Pasta {:7.2}",
        secs(total(&t_bb)) * 1e9 / n_cells as f64,
        secs(total(&t_bn)) * 1e9 / n_cells as f64,
        secs(total(&t_mn)) * 1e9 / n_cells as f64
    );
}

// ============================================================================
// [3] LDE + Merkle — the control that the LDE is config-independent
// ============================================================================

#[test]
#[ignore = "MEASUREMENT: the coset-LDE share, and the control that it does not move with the hash."]
fn hash_swap_lde_share_is_config_independent() {
    let shrink = shrink_from_env();
    let rounds = root_rounds(shrink);
    println!("=== [3] commit (LDE + Merkle) vs commit_ldes (Merkle) — SHRINK={shrink} ===");

    let bb = at_root_knobs!(create_recursion_config_with_fri);
    let c_bb = total(&commit_full(&bb, &rounds));
    let m_bb = total(&merkle_only(&bb, &rounds));
    drop(bb);
    let bn = at_root_knobs!(create_outer_config_with_fri);
    let c_bn = total(&commit_full(&bn, &rounds));
    let m_bn = total(&merkle_only(&bn, &rounds));
    drop(bn);
    let mn = at_root_knobs!(create_mina_config_with_fri);
    let c_mn = total(&commit_full(&mn, &rounds));
    let m_mn = total(&merkle_only(&mn, &rounds));

    println!("            commit(LDE+Merkle)   commit_ldes(Merkle)   implied LDE");
    println!(
        "BabyBear  {:14.2} s {:19.2} s {:12.2} s",
        secs(c_bb),
        secs(m_bb),
        secs(c_bb) - secs(m_bb)
    );
    println!(
        "BN254     {:14.2} s {:19.2} s {:12.2} s",
        secs(c_bn),
        secs(m_bn),
        secs(c_bn) - secs(m_bn)
    );
    println!(
        "Pasta     {:14.2} s {:19.2} s {:12.2} s",
        secs(c_mn),
        secs(m_mn),
        secs(c_mn) - secs(m_mn)
    );
    println!(
        "⚑ the three implied-LDE figures must agree; a spread is the error bar on this method."
    );
}

// ============================================================================
// [4] The whole opening argument — commit + FRI commit phase + queries + PoW
// ============================================================================

#[test]
#[ignore = "MEASUREMENT: the FRI half. commit_ldes + open under all three hashes."]
fn hash_swap_open_at_root_geometry() {
    let shrink = shrink_from_env();
    let rounds = root_rounds(shrink);
    println!(
        "=== [4] commit_ldes + open — SHRINK={shrink}, {ROOT_NUM_QUERIES} queries, {ROOT_QUERY_POW_BITS} PoW bits ==="
    );

    let bb = at_root_knobs!(create_recursion_config_with_fri);
    let s_bb = commit_and_open(&bb, &rounds);
    drop(bb);
    println!(
        "BabyBear  merkle {:8.2} s  open {:8.2} s  proof {:9} B",
        secs(s_bb.merkle),
        secs(s_bb.open),
        s_bb.proof_bytes
    );

    let bn = at_root_knobs!(create_outer_config_with_fri);
    let s_bn = commit_and_open(&bn, &rounds);
    drop(bn);
    println!(
        "BN254     merkle {:8.2} s  open {:8.2} s  proof {:9} B",
        secs(s_bn.merkle),
        secs(s_bn.open),
        s_bn.proof_bytes
    );

    let mn = at_root_knobs!(create_mina_config_with_fri);
    let s_mn = commit_and_open(&mn, &rounds);
    println!(
        "Pasta     merkle {:8.2} s  open {:8.2} s  proof {:9} B",
        secs(s_mn.merkle),
        secs(s_mn.open),
        s_mn.proof_bytes
    );

    let tot = |s: &Split| secs(s.merkle) + secs(s.open);
    println!("--- totals (commit_ldes + open) ---");
    println!(
        "BabyBear {:8.2} s   BN254 {:8.2} s   Pasta {:8.2} s",
        tot(&s_bb),
        tot(&s_bn),
        tot(&s_mn)
    );
    println!("Pasta / BabyBear : {:.2}x", tot(&s_mn) / tot(&s_bb));
    println!("Pasta / BN254    : {:.2}x", tot(&s_mn) / tot(&s_bn));
    println!("--- proof bytes ---");
    println!(
        "Pasta / BabyBear : {:.3}x",
        s_mn.proof_bytes as f64 / s_bb.proof_bytes as f64
    );
    println!("--- where the delta lands ---");
    let d_merkle = secs(s_mn.merkle) - secs(s_bb.merkle);
    let d_open = secs(s_mn.open) - secs(s_bb.open);
    println!(
        "delta in commit-phase Merkle : {d_merkle:8.2} s ({:.1}%)",
        100.0 * d_merkle / (d_merkle + d_open)
    );
    println!(
        "delta in open (FRI + queries): {d_open:8.2} s ({:.1}%)",
        100.0 * d_open / (d_merkle + d_open)
    );
}

/// `commit_ldes` under an arbitrary config, rendered as a string — the only way
/// to compare three commitments whose *types* differ by construction.
fn commitment_debug<SC>(config: &SC, mats: Vec<RowMajorMatrix<BabyBear>>) -> String
where
    SC: StarkGenericConfig<Challenge = EF>,
    SC::Pcs: Pcs<EF, SC::Challenger, Domain = TwoAdicMultiplicativeCoset<BabyBear>>,
    <SC::Pcs as Pcs<EF, SC::Challenger>>::Commitment: core::fmt::Debug,
{
    let (c, _data) = <SC::Pcs as Pcs<EF, SC::Challenger>>::commit_ldes(config.pcs(), mats);
    format!("{c:?}")
}

/// A cheap non-`#[ignore]` gate so the file is compiled and run by the normal
/// suite: the three configs must genuinely disagree on the digest of one fixed
/// matrix. If a config's hash silently became another's, every number above
/// would be a comparison of one hash with itself.
#[test]
fn hash_swap_three_configs_commit_to_three_different_roots() {
    let rounds = vec![vec![(6usize, 4usize, 1usize)]];
    let mats = || build_round(&rounds[0], 0xC0FFEE);

    let bb = at_root_knobs!(create_recursion_config_with_fri);
    let bn = at_root_knobs!(create_outer_config_with_fri);
    let mn = at_root_knobs!(create_mina_config_with_fri);

    let s_bb = commitment_debug(&bb, mats());
    let s_bn = commitment_debug(&bn, mats());
    let s_mn = commitment_debug(&mn, mats());
    assert_ne!(s_bb, s_bn, "BabyBear and BN254 commitments coincide");
    assert_ne!(s_bb, s_mn, "BabyBear and Pasta commitments coincide");
    assert_ne!(s_bn, s_mn, "BN254 and Pasta commitments coincide");

    // And the geometry the measurements use is the deployed root's, not a guess.
    let r = root_rounds(0);
    assert_eq!(r.len(), 4, "the root commits four rounds");
    assert_eq!(r[0].len(), 7, "seven instances in the main round");
    assert_eq!(r[1].len(), 14, "two quotient chunks per instance");
    assert_eq!(
        r.iter().flat_map(|x| x.iter()).map(|&(lh, _, _)| lh).max(),
        Some(22),
        "logGlobalMaxHeight is 22"
    );
}
