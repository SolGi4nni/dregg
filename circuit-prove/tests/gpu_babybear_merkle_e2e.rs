//! THE FOLD'S GPU MERKLE LEVER: parity + speed for `GpuBabyBearMmcs` (the
//! Poseidon2-BabyBear-W16 GPU Merkle tree) and `GpuDft` on BabyBear — the two
//! PCS seams that dominate the ~288s recursive fold (`prove_turn_chain_recursive`
//! commits under `MerkleTreeMmcs<..PaddingFreeSponge<Perm,16,8,8>..>` + a
//! `Radix2DitParallel` DFT).
//!
//! PARITY IS LOAD-BEARING (the shrink discipline): every GPU commit must produce
//! the BYTE-IDENTICAL Merkle root as the CPU `MerkleTreeMmcs`, and a GPU-minted
//! opening must verify under the untouched CPU verifier — a fast wrong tree is
//! worthless. Parity is asserted before any timing is reported.
//!
//! Run (release, GPU present):
//!   cargo test -p dregg-circuit-prove --release --test gpu_babybear_merkle_e2e -- --ignored --nocapture

use std::time::Instant;

use dregg_circuit_prove::gpu_backend::{BbValMmcs, GpuBabyBearMmcs, GpuDft};
use p3_baby_bear::{BabyBear, default_babybear_poseidon2_16};
use p3_commit::Mmcs;
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::integers::QuotientMap;
use p3_field::{Field, PrimeField32};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};

type BbPerm = p3_baby_bear::Poseidon2BabyBear<16>;

fn cpu_mmcs() -> BbValMmcs {
    let perm = default_babybear_poseidon2_16();
    let hash = PaddingFreeSponge::<BbPerm, 16, 8, 8>::new(perm.clone());
    let compress = TruncatedPermutation::<BbPerm, 2, 8, 16>::new(perm);
    BbValMmcs::new(hash, compress, 0)
}

/// Deterministic xorshift BabyBear matrix (no rand-version friction).
fn rand_matrix(seed: u64, rows: usize, cols: usize) -> RowMajorMatrix<BabyBear> {
    let mut s = seed | 1;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let values: Vec<BabyBear> = (0..rows * cols)
        .map(|_| BabyBear::from_int((next() % 0x7800_0001) as u32))
        .collect();
    RowMajorMatrix::new(values, cols)
}

/// THE GPU LANE IS FAIL-CLOSED (the crate's own better pattern, `gpu_backend.rs`'s
/// `assert!(gpu_mmcs.adapter_available())`).
///
/// This used to be `Option<..>` + `eprintln!("no GPU adapter — skipping"); return;` at both call
/// sites — which reported **`ok`** having verified NOTHING, in a file whose own module doc says
/// "PARITY IS LOAD-BEARING... a fast wrong tree is worthless." A green that means nothing is worse
/// than a red. The honest posture is ONE law, both halves required:
///   * `#[ignore]` — so a GPU-less runner reports these as SKIPPED, explicitly, in its summary;
///   * this hard assert — so once a runner DOES opt in via `--ignored`, an absent adapter is a
///     LOUD failure and can never degenerate into a silent no-op.
///
/// Run it with `scripts/test-gauntlet.sh gpu` on a box that has an adapter. HONEST SCOPE: there is
/// NO scheduled GPU lane — GitHub-hosted runners have no usable adapter, so these teeth are
/// human-invoked on a GPU box today. Wiring a nightly lane needs a self-hosted GPU runner; that is
/// named as the open lane in `.github/workflows/armed-teeth.yml`'s header, not implied here.
fn require_gpu() -> GpuBabyBearMmcs {
    let m = GpuBabyBearMmcs::new(0);
    assert!(
        m.adapter_available(),
        "no GPU adapter — this parity gate must RUN on the GPU lane, never silently skip. It is \
         `#[ignore]`d precisely so a GPU-less runner skips it EXPLICITLY; reaching this assert \
         means the lane opted in with `--ignored` on a host with no adapter. Run it on the GPU box \
         (`scripts/test-gauntlet.sh gpu`) or drop `--ignored` here."
    );
    m
}

#[test]
#[ignore = "GPU + slow: run on the GPU lane with --ignored --nocapture (fail-CLOSED: asserts adapter_available())"]
fn gpu_babybear_merkle_parity_and_speed() {
    let gpu = require_gpu();
    let cpu = cpu_mmcs();
    println!("=== GpuBabyBearMmcs: Poseidon2-BabyBear-W16 GPU Merkle ===");

    // ---- PARITY 1: single matrix (multi-height sweep) ----
    for log_h in [14usize, 16, 18] {
        let h = 1 << log_h;
        for w in [8usize, 100, 256] {
            let m = rand_matrix(0xA11CE + (log_h as u64) * 131 + w as u64, h, w);
            let (c_cpu, _) = cpu.commit(vec![m.clone()]);
            let (c_gpu, _) = gpu.commit(vec![m]);
            assert_eq!(
                c_cpu, c_gpu,
                "root mismatch at single matrix h=2^{log_h} w={w}"
            );
        }
    }
    println!("parity 1 OK: single-matrix roots byte-identical (h=2^14..18, w in {{8,100,256}})");

    // ---- PARITY 2: multi-matrix, multi-height batch (grouping + injection) ----
    let batch = || {
        vec![
            rand_matrix(1, 1 << 16, 231), // tallest group, mat A
            rand_matrix(2, 1 << 16, 64),  // tallest group, mat B (same height)
            rand_matrix(3, 1 << 15, 40),  // injected one level down
            rand_matrix(4, 1 << 13, 200), // injected three levels down
        ]
    };
    let (c_cpu, _) = cpu.commit(batch());
    let (c_gpu, dgpu) = gpu.commit(batch());
    assert_eq!(
        c_cpu, c_gpu,
        "root mismatch on multi-height injection batch"
    );
    println!("parity 2 OK: multi-height + injection root byte-identical");

    // ---- PARITY 3: a GPU-minted opening verifies under the CPU verifier ----
    let mats = batch();
    let dims: Vec<p3_matrix::Dimensions> = mats.iter().map(|m| m.dimensions()).collect();
    for index in [0usize, 1, 12345, (1 << 16) - 1] {
        let op = gpu.open_batch(index, &dgpu);
        let (ov, proof) = (op.opened_values.clone(), op.opening_proof.clone());
        gpu.verify_batch(
            &c_gpu,
            &dims,
            index,
            p3_commit::BatchOpeningRef::new(&ov, &proof),
        )
        .unwrap_or_else(|e| {
            panic!("GPU-minted opening at index {index} rejected by CPU verifier: {e:?}")
        });
    }
    println!("parity 3 OK: GPU-minted openings verify under the untouched CPU verifier");

    // ---- MEASURE: GPU vs CPU commit wall-time (parity re-asserted each) ----
    println!("\n-- Merkle commit: GPU vs CPU (best-of-3, parity-gated) --");
    println!(
        "  (leaf = PaddingFreeSponge<Perm,16,8,8>; compress = TruncatedPermutation<Perm,2,8,16>)"
    );
    let width = 256usize;
    let mut rows = Vec::new();
    for log_h in [16usize, 18, 20] {
        let h = 1 << log_h;
        let m = rand_matrix(0xBEEF + log_h as u64, h, width);

        // warm both, then best-of-3
        let (c0, _) = cpu.commit(vec![m.clone()]);
        let (g0, _) = gpu.commit(vec![m.clone()]);
        assert_eq!(c0, g0, "root mismatch at measure h=2^{log_h}");

        let mut cpu_s = f64::MAX;
        let mut gpu_s = f64::MAX;
        for _ in 0..3 {
            let t = Instant::now();
            let (_c, _d) = cpu.commit(vec![m.clone()]);
            cpu_s = cpu_s.min(t.elapsed().as_secs_f64());
            let t = Instant::now();
            let (_c, _d) = gpu.commit(vec![m.clone()]);
            gpu_s = gpu_s.min(t.elapsed().as_secs_f64());
        }
        let hashes = (2 * h - 1) as f64;
        println!(
            "  h=2^{log_h:<2} w={width}: CPU {:8.2} ms ({:6.1} Mhash/s) | GPU {:8.2} ms ({:6.1} Mhash/s) | speedup {:.2}x",
            cpu_s * 1e3,
            hashes / cpu_s / 1e6,
            gpu_s * 1e3,
            hashes / gpu_s / 1e6,
            cpu_s / gpu_s,
        );
        rows.push((log_h, cpu_s, gpu_s));
    }
    if let Some((_, cs, gs)) = rows.iter().max_by(|a, b| a.0.cmp(&b.0)) {
        println!(
            "  => Merkle-build GPU speedup at the largest measured height: {:.2}x",
            cs / gs
        );
    }
}

#[test]
#[ignore = "GPU + slow: run on the GPU lane with --ignored --nocapture (fail-CLOSED: asserts adapter_name())"]
fn gpu_babybear_dft_parity_and_speed() {
    // Confirm the SHRINK's GpuDft serves the FOLD's BabyBear DFT (it is native
    // BabyBear): byte-identical coset LDE vs the fold's `Radix2DitParallel`,
    // plus wall-time. (The fold's PCS commits `coset_lde_batch` at log_blowup.)
    let gpu = GpuDft::default();
    // Fail-CLOSED, same law as `require_gpu` above: absent adapter ⇒ LOUD, never a hollow `ok`.
    let name = gpu.adapter_name().expect(
        "no GPU adapter — this DFT parity gate must RUN on the GPU lane, never silently skip. It \
         is `#[ignore]`d so a GPU-less runner skips it EXPLICITLY; reaching this means the lane \
         opted in with `--ignored` on a host with no adapter.",
    );
    println!("=== GpuDft on BabyBear (fold DFT lever) — adapter: {name} ===");
    let cpu = Radix2DitParallel::<BabyBear>::default();
    let shift = BabyBear::GENERATOR;
    let added = 1usize; // log_blowup shape

    let width = 256usize;
    for log_h in [16usize, 18, 20] {
        let h = 1 << log_h;
        let m = rand_matrix(0xD57 + log_h as u64, h, width);

        let cpu_ev = cpu
            .coset_lde_batch(m.clone(), added, shift)
            .to_row_major_matrix();
        let gpu_ev = gpu
            .coset_lde_batch(m.clone(), added, shift)
            .to_row_major_matrix();
        assert_eq!(
            cpu_ev
                .values
                .iter()
                .map(|x| x.as_canonical_u32())
                .collect::<Vec<_>>(),
            gpu_ev
                .values
                .iter()
                .map(|x| x.as_canonical_u32())
                .collect::<Vec<_>>(),
            "GpuDft coset LDE mismatch at h=2^{log_h}"
        );

        let mut cpu_s = f64::MAX;
        let mut gpu_s = f64::MAX;
        for _ in 0..3 {
            let t = Instant::now();
            let _ = cpu
                .coset_lde_batch(m.clone(), added, shift)
                .to_row_major_matrix();
            cpu_s = cpu_s.min(t.elapsed().as_secs_f64());
            let t = Instant::now();
            let _ = gpu
                .coset_lde_batch(m.clone(), added, shift)
                .to_row_major_matrix();
            gpu_s = gpu_s.min(t.elapsed().as_secs_f64());
        }
        println!(
            "  h=2^{log_h:<2} w={width}: parity OK | CPU {:8.2} ms | GPU {:8.2} ms | speedup {:.2}x",
            cpu_s * 1e3,
            gpu_s * 1e3,
            cpu_s / gpu_s,
        );
    }
}
