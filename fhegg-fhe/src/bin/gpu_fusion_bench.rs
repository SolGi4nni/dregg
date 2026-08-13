//! THE FUSION MEASUREMENT.
//!
//! Thesis under test: *a vFHE prover's multilinear evaluation tables ARE the FHE evaluation's
//! intermediates, so a fused pipeline pays the memory traffic once.* If that does not win at toy
//! scale on a GPU it will not win on an FPGA.
//!
//! The experiment is a BFV RNS fold-add producing a device-resident ciphertext, followed by a
//! sumcheck MLE fold that consumes it — run two ways that compute the SAME field element (asserted
//! every iteration, not just in the test suite):
//!
//! * **FUSED** — `fold_resident` -> `bridge_to_babybear` -> `mle_fold_rounds` -> one 4-byte
//!   readback. The ciphertext never leaves the device.
//! * **UNFUSED** — `fold_resident` -> `download` (full ciphertext to the host) -> host-side limb
//!   encoding -> `upload_table` -> `mle_fold_rounds` -> one 4-byte readback.
//!
//! Both paths run identical GPU kernels over identical data. The ONLY difference is the round trip,
//! so the delta is the round trip.
//!
//! Two more columns exist so the ratio cannot be misread. `dl_us` / `encup_us` split the round trip
//! into "bytes down + host reassembly" and "host encode + bytes up", and `cpu_mle_us` folds the same
//! table on the host so the GPU leg's own worth is visible.
//!
//! ⚑ And [`sync_floor`] measures what ONE device synchronization costs when almost no bytes cross.
//! On the measured adapter that is ~1.3 ms, which dominates every small size — read it before
//! reading any speedup, or bandwidth gets credit for a stall. [`multi_stage`] then sweeps K, where
//! the fused path amortizes that stall over K stages and the unfused path cannot.
//!
//! Run: `cargo run -p fhegg-fhe --release --bin gpu_fusion_bench`
//! Debug timings are meaningless; the binary refuses to run in debug.

use std::time::{Duration, Instant};

use fhegg_fhe::bfv_lean::{LeanCiphertext, RnsPoly, FOLD_MODULI};
use fhegg_fhe::gpu_arena::{arena, Arena, ResidentHandle};
use fhegg_fhe::mle_gpu::{
    bridge_lanes_to_babybear, fixture_challenges, fold_mle_all, table_len_for_lanes,
};

/// One measured configuration.
struct Case {
    /// Polynomial degree. 4096 is the deployed `FOLD_DEGREE`; the rest are synthetic scale.
    degree: usize,
    /// Ciphertexts folded into one before the prover sees anything.
    n_cts: usize,
}

const CASES: &[Case] = &[
    Case {
        degree: 256,
        n_cts: 8,
    },
    Case {
        degree: 1024,
        n_cts: 8,
    },
    Case {
        degree: 4096,
        n_cts: 8,
    },
    Case {
        degree: 16384,
        n_cts: 8,
    },
    Case {
        degree: 65536,
        n_cts: 8,
    },
    Case {
        degree: 262_144,
        n_cts: 4,
    },
];

const REPS: usize = 11;

fn synth_ct(seed: u64, degree: usize) -> LeanCiphertext {
    let mut s = seed;
    let mut next = || {
        s = s
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .rotate_left(17)
            .wrapping_add(1);
        s
    };
    let polys = (0..2)
        .map(|_| RnsPoly {
            rows: FOLD_MODULI
                .iter()
                .map(|&q| (0..degree).map(|_| next() % q).collect())
                .collect(),
        })
        .collect();
    LeanCiphertext {
        moduli: FOLD_MODULI.to_vec(),
        degree,
        level: 0,
        variable_time: false,
        polys,
        plain_bound: 1,
    }
}

fn lanes_of(ct: &LeanCiphertext) -> Vec<u64> {
    ct.polys
        .iter()
        .flat_map(|p| p.rows.iter().flat_map(|r| r.iter().copied()))
        .collect()
}

fn median(mut xs: Vec<Duration>) -> Duration {
    xs.sort_unstable();
    xs[xs.len() / 2]
}

/// FUSED: bridge and fold without the ciphertext ever touching the host.
fn fused(a: &Arena, folded: &ResidentHandle, challenges: &[u32]) -> u32 {
    let mut table = a.bridge_to_babybear(folded);
    a.mle_fold_rounds(&mut table, challenges);
    a.download_table(&table)[0]
}

/// UNFUSED: the ciphertext comes back to the host, is encoded there, and goes up again.
fn unfused(a: &Arena, folded: &ResidentHandle, table_len: usize, challenges: &[u32]) -> u32 {
    let downloaded = a.download(folded);
    let host_table = bridge_lanes_to_babybear(&lanes_of(&downloaded[0]), table_len);
    let mut table = a.upload_table(&host_table);
    a.mle_fold_rounds(&mut table, challenges);
    a.download_table(&table)[0]
}

/// Half the round trip: the ciphertext down to the host (staging copy, map, wait, and the
/// `LeanCiphertext` reassembly a caller actually receives).
fn download_only(a: &Arena, folded: &ResidentHandle) -> usize {
    a.download(folded)[0].degree
}

/// The other half: host-side limb encoding plus the upload of the resulting table.
fn encode_and_upload(a: &Arena, ct: &LeanCiphertext, table_len: usize) -> usize {
    let host_table = bridge_lanes_to_babybear(&lanes_of(ct), table_len);
    a.upload_table(&host_table).len()
}

fn main() {
    if cfg!(debug_assertions) {
        eprintln!("REFUSED: build with --release. Debug timings measure rustc, not the GPU.");
        std::process::exit(2);
    }
    let Some(a) = arena() else {
        eprintln!("no wgpu adapter — fusion bench cannot run (headless)");
        std::process::exit(1);
    };

    println!("# WGSL fusion measurement — BFV fold_resident -> MLE fold over BabyBear");
    // Name the silicon in the artifact. A fusion delta on unified memory means something different
    // from the same delta across a PCIe link, and a reader should not have to guess which they have.
    let instance = wgpu::Instance::default();
    if let Some(adapter) =
        pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))
    {
        let info = adapter.get_info();
        let limits = adapter.limits();
        println!(
            "# adapter: {} [{:?} / {:?}]  max_storage_binding={} max_buffer={}",
            info.name,
            info.device_type,
            info.backend,
            limits.max_storage_buffer_binding_size,
            limits.max_buffer_size
        );
    }
    println!("# median of {REPS} reps, wall clock including the device wait");
    println!(
        "# {:>7} {:>5} {:>10} {:>9} {:>5} {:>9} {:>10} {:>10} {:>9} {:>9} {:>10} {:>7}",
        "degree",
        "n_ct",
        "ct_bytes",
        "lanes",
        "vars",
        "table_len",
        "fused_us",
        "unfused_us",
        "dl_us",
        "encup_us",
        "cpu_mle_us",
        "speedup"
    );

    for case in CASES {
        let cts: Vec<_> = (0..case.n_cts)
            .map(|i| synth_ct(i as u64 + 1, case.degree))
            .collect();
        let ct_bytes = 2 * FOLD_MODULI.len() * case.degree * 8;
        let lanes = 2 * FOLD_MODULI.len() * case.degree;
        let table_len = table_len_for_lanes(lanes);
        let n_vars = table_len.trailing_zeros() as usize;
        let challenges = fixture_challenges(n_vars, 0xF05E ^ case.degree as u64);

        // The prover's input: one BFV fold, resident. Both paths start from the SAME handle, so the
        // fold itself is outside the comparison — what is being compared is what happens next.
        let uploaded = a.upload(&cts);
        let folded = a.fold_resident(&uploaded);
        a.wait_idle();

        // Parity, every size: if the two paths disagree the delta below is meaningless.
        let fused_value = fused(&a, &folded, &challenges);
        let unfused_value = unfused(&a, &folded, table_len, &challenges);
        assert_eq!(
            fused_value, unfused_value,
            "degree {}: fused and unfused disagree — the measurement is comparing two computations",
            case.degree
        );
        // And against a pure-CPU fold of the same table, so neither GPU path is self-consistent-but-wrong.
        let host_table = bridge_lanes_to_babybear(&lanes_of(&a.download(&folded)[0]), table_len);
        assert_eq!(
            fused_value,
            fold_mle_all(&host_table, &challenges),
            "degree {}: GPU pipelines disagree with the CPU reference",
            case.degree
        );

        let mut fused_times = Vec::with_capacity(REPS);
        let mut unfused_times = Vec::with_capacity(REPS);
        let mut dl_times = Vec::with_capacity(REPS);
        let mut encup_times = Vec::with_capacity(REPS);
        let mut cpu_times = Vec::with_capacity(REPS);
        let downloaded_ct = a.download(&folded).pop().expect("one folded ciphertext");

        for _ in 0..REPS {
            a.wait_idle();
            let t = Instant::now();
            let v = fused(&a, &folded, &challenges);
            fused_times.push(t.elapsed());
            std::hint::black_box(v);

            a.wait_idle();
            let t = Instant::now();
            let v = unfused(&a, &folded, table_len, &challenges);
            unfused_times.push(t.elapsed());
            std::hint::black_box(v);

            // The round trip, split so "bytes moved" and "host reassembly + encode" are separable
            // rather than asserted.
            a.wait_idle();
            let t = Instant::now();
            let n = download_only(&a, &folded);
            dl_times.push(t.elapsed());
            std::hint::black_box(n);

            let t = Instant::now();
            let n = encode_and_upload(&a, &downloaded_ct, table_len);
            encup_times.push(t.elapsed());
            std::hint::black_box(n);

            let t = Instant::now();
            let v = fold_mle_all(&host_table, &challenges);
            cpu_times.push(t.elapsed());
            std::hint::black_box(v);
        }

        let f = median(fused_times);
        let u = median(unfused_times);
        let dl = median(dl_times);
        let encup = median(encup_times);
        let c = median(cpu_times);
        println!(
            "  {:>7} {:>5} {:>10} {:>9} {:>5} {:>9} {:>10.1} {:>10.1} {:>9.1} {:>9.1} {:>10.1} {:>6.2}x",
            case.degree,
            case.n_cts,
            ct_bytes,
            lanes,
            n_vars,
            table_len,
            f.as_secs_f64() * 1e6,
            u.as_secs_f64() * 1e6,
            dl.as_secs_f64() * 1e6,
            encup.as_secs_f64() * 1e6,
            c.as_secs_f64() * 1e6,
            u.as_secs_f64() / f.as_secs_f64()
        );

        // Handles die with the pools; nothing above outlives this point.
        drop(folded);
        drop(uploaded);
        a.clear_pool();
    }

    sync_floor(&a);
    multi_stage(&a);
}

/// THE FIXED COST, measured rather than inferred. The smallest possible pipeline — a 2-element
/// table, one fold round, one readback — isolates what a device synchronization costs when almost
/// no bytes cross. Every row above is sitting on top of this number, and reading the table without
/// it invites the wrong conclusion (that a fusion win at small sizes is about bandwidth).
fn sync_floor(a: &Arena) {
    let mut waits = Vec::with_capacity(REPS);
    let mut pipelines = Vec::with_capacity(REPS);
    for _ in 0..REPS {
        a.wait_idle();
        let t = Instant::now();
        a.wait_idle();
        waits.push(t.elapsed());

        a.wait_idle();
        let t = Instant::now();
        let mut table = a.upload_table(&[1, 2]);
        a.mle_fold_rounds(&mut table, &[3]);
        let v = a.download_table(&table)[0];
        pipelines.push(t.elapsed());
        std::hint::black_box(v);
    }
    a.clear_pool();
    println!();
    println!("# fixed costs (nothing to do with bytes):");
    println!(
        "#   idle wait_idle():                       {:>9.1} us",
        median(waits).as_secs_f64() * 1e6
    );
    println!(
        "#   minimal pipeline (2 elems, 1 round):    {:>9.1} us  <- the per-synchronization floor",
        median(pipelines).as_secs_f64() * 1e6
    );
}

/// DOES THE WIN COMPOUND? One hand-off is one hand-off; a real vFHE pipeline absorbs a BATCH of FHE
/// outputs. Fused, K stages are K sets of dispatches and ONE synchronization. Unfused, they are K
/// host round trips and K+1 synchronizations. If fusion is a real structural win rather than a
/// one-off constant, the ratio must grow with K.
fn multi_stage(a: &Arena) {
    const DEGREE: usize = 4096; // the deployed FOLD_DEGREE
    const STAGE_CTS: usize = 4;

    let lanes = 2 * FOLD_MODULI.len() * DEGREE;
    let table_len = table_len_for_lanes(lanes);
    let n_vars = table_len.trailing_zeros() as usize;
    let challenges = fixture_challenges(n_vars, 0x5A6E);

    println!();
    println!("# K independent FHE outputs absorbed by the prover, degree {DEGREE} ({table_len}-element tables)");
    println!(
        "# {:>4} {:>12} {:>12} {:>12} {:>12} {:>8}",
        "K", "fused_us", "unfused_us", "fused/stage", "unfsd/stage", "speedup"
    );

    for k in [1usize, 2, 4, 8, 16] {
        let handles: Vec<_> = (0..k)
            .map(|s| {
                let cts: Vec<_> = (0..STAGE_CTS)
                    .map(|i| synth_ct((s * 97 + i + 1) as u64, DEGREE))
                    .collect();
                a.fold_resident(&a.upload(&cts))
            })
            .collect();
        a.wait_idle();

        // Parity before timing.
        let f0 = fused_batch(a, &handles, &challenges);
        let u0 = unfused_batch(a, &handles, table_len, &challenges);
        assert_eq!(f0, u0, "K={k}: fused and unfused batches disagree");

        let mut fused_times = Vec::with_capacity(REPS);
        let mut unfused_times = Vec::with_capacity(REPS);
        for _ in 0..REPS {
            a.wait_idle();
            let t = Instant::now();
            let v = fused_batch(a, &handles, &challenges);
            fused_times.push(t.elapsed());
            std::hint::black_box(v);

            a.wait_idle();
            let t = Instant::now();
            let v = unfused_batch(a, &handles, table_len, &challenges);
            unfused_times.push(t.elapsed());
            std::hint::black_box(v);
        }
        let f = median(fused_times).as_secs_f64() * 1e6;
        let u = median(unfused_times).as_secs_f64() * 1e6;
        println!(
            "  {:>4} {:>12.1} {:>12.1} {:>12.1} {:>12.1} {:>7.2}x",
            k,
            f,
            u,
            f / k as f64,
            u / k as f64,
            u / f
        );
        drop(handles);
        a.clear_pool();
    }
}

/// K stages, everything resident, ONE synchronization at the end.
fn fused_batch(a: &Arena, handles: &[ResidentHandle], challenges: &[u32]) -> Vec<u32> {
    let tables: Vec<_> = handles
        .iter()
        .map(|h| {
            let mut t = a.bridge_to_babybear(h);
            a.mle_fold_rounds(&mut t, challenges);
            t
        })
        .collect();
    let refs: Vec<&_> = tables.iter().collect();
    a.download_tables(&refs).into_iter().map(|v| v[0]).collect()
}

/// K stages, each round-tripped through the host, then the same single gathered readback — so the
/// ONLY thing the comparison charges the unfused path for is the round trip itself.
fn unfused_batch(
    a: &Arena,
    handles: &[ResidentHandle],
    table_len: usize,
    challenges: &[u32],
) -> Vec<u32> {
    let tables: Vec<_> = handles
        .iter()
        .map(|h| {
            let downloaded = a.download(h);
            let host_table = bridge_lanes_to_babybear(&lanes_of(&downloaded[0]), table_len);
            let mut t = a.upload_table(&host_table);
            a.mle_fold_rounds(&mut t, challenges);
            t
        })
        .collect();
    let refs: Vec<&_> = tables.iter().collect();
    a.download_tables(&refs).into_iter().map(|v| v[0]).collect()
}
