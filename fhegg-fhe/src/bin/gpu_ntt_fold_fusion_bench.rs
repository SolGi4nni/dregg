//! WHAT THE DEVICE CONSOLIDATION UNLOCKED — the NTT -> fold hand-off, measured.
//!
//! The prior lane (`~/dev/zkml-research/notes/wgpu-fusion.md`) measured fusion across the one seam
//! that was reachable — a BFV fold feeding an MLE fold, both inside `Arena`'s single device — and
//! found 2.7x–7.1x at 2^20–2^22 on memory traffic alone, compounding to a 3.8x–5.3x per-stage fall
//! over K=1..16. It also named why nothing else could be measured: `bfv_ntt_gpu` stood up its own
//! `wgpu::Device`, and two wgpu devices cannot share a buffer.
//!
//! `gpu_device` put every kernel in this crate on one device. This binary measures the two seams
//! that opened as a result, in the same shape as `gpu_fusion_bench`:
//!
//! * **PAIR A — NTT -> fold.** A batch of forward negacyclic NTTs feeding the RNS fold-add. This is
//!   the deployed BFV aggregation shape: transform, then aggregate. FUSED adopts the NTT's own
//!   output buffer; UNFUSED reads it back to the host as `RnsPoly`s and uploads them again, which
//!   is what the code did before today because it had no other choice.
//! * **PAIR B — NTT -> fold -> bridge -> MLE fold.** The whole vFHE chain: three kernels from two
//!   modules, two seams, one device. Before the consolidation this needed two devices and was
//!   unreachable twice over.
//!
//! Both paths of both pairs compute the same value and it is **asserted every case**, so the delta
//! is the round trip and nothing else. Median of `REPS`, fused and unfused interleaved rep by rep.
//!
//! ⚠ TWO CAVEATS THAT MUST TRAVEL WITH EVERY NUMBER HERE.
//!
//! 1. **This machine has unified memory.** A "download" is a copy inside one physical DRAM with no
//!    bus crossing, so every figure is a **LOWER BOUND** — a discrete GPU pays a real transfer each
//!    way and an FPGA spilling to off-chip DRAM pays worse.
//! 2. **The ~1–2.5 ms synchronization floor is wgpu's, not physics.** [`sync_floor`] measures it
//!    and every table prints the traffic-only figure beside the raw one. Carry the traffic-only
//!    column into any hardware argument; the raw column silently credits bandwidth for one fewer
//!    stall.
//!
//! Run: `cargo run -p fhegg-fhe --release --bin gpu_ntt_fold_fusion_bench`

use std::time::{Duration, Instant};

use fhegg_fhe::bfv_lean::{LeanCiphertext, RnsPoly, FOLD_MODULI};
use fhegg_fhe::bfv_ntt_gpu::RnsNttEngine;
use fhegg_fhe::gpu_arena::{arena, Arena};
use fhegg_fhe::mle_gpu::{bridge_lanes_to_babybear, fixture_challenges, table_len_for_lanes};

/// (degree, polynomials-per-batch) swept.
///
/// ⚑ The sweep grows the BATCH, not the degree, past 4096. That is not a stylistic choice: the
/// deployed `FOLD_MODULI` admit a negacyclic NTT only up to the deployed `FOLD_DEGREE` — at 16384
/// `fhe-math` refuses with "Impossible to construct a Ntt operator", because q ≢ 1 mod 2N. Growing
/// the batch reaches the same byte counts through the shape a real aggregation actually has (many
/// ciphertexts at one degree) instead of a degree the deployed parameters cannot express.
const CASES: &[(usize, usize)] = &[
    (256, 8),
    (1024, 8),
    (4096, 8),
    (4096, 32),
    (4096, 128),
    (4096, 512),
];

const REPS: usize = 11;

/// K-sweep for the compounding result: how many independent NTT->fold stages the pipeline absorbs
/// before it synchronizes.
const STAGE_COUNTS: &[usize] = &[1, 2, 4, 8, 16];

/// Batch used by the K-sweep, at the deployed degree.
const STAGE_BATCH: usize = 32;

/// ⚑ HOW A SUBTRACTED RATIO IS ALLOWED TO BE PRINTED.
///
/// `traffic` divides two numbers that have each had ~1.8 ms of synchronization removed. When the
/// measurement itself is ~1.8 ms, that denominator is noise and the quotient is a fantasy — an
/// early run of this binary printed **1541x** for a case whose raw speedup was 1.88x. Quoting the
/// flattering half of a pair is exactly how a nothing result reads as a triumph, so the ratio is
/// printed only when BOTH arms clear the floor by this factor, and `—` otherwise.
const FLOOR_HEADROOM: f64 = 2.0;

/// The traffic-only ratio, or `None` when the subtraction is not reliable at this size.
fn traffic_ratio(fused: f64, unfused: f64, floor: f64) -> Option<f64> {
    if fused <= floor * FLOOR_HEADROOM || unfused <= floor * FLOOR_HEADROOM {
        return None;
    }
    Some((unfused - floor) / (fused - floor))
}

fn show(ratio: Option<f64>) -> String {
    ratio.map_or_else(|| "—".to_owned(), |r| format!("{r:.2}x"))
}

fn synth_poly(seed: u64, degree: usize) -> RnsPoly {
    let mut state = seed;
    RnsPoly {
        rows: FOLD_MODULI
            .iter()
            .map(|&q| {
                (0..degree)
                    .map(|i| {
                        state = state
                            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                            .rotate_left(17)
                            .wrapping_add(i as u64 + 1);
                        state % q
                    })
                    .collect()
            })
            .collect(),
    }
}

/// A BFV ciphertext is a PAIR of polynomials — the deployed shape, and the only one
/// `bfv_lean::fold` accepts. The NTT batch is therefore always an even number of polynomials,
/// consumed two at a time; the buffer layout is unaffected because `[polynomial][rns row]
/// [coefficient]` is contiguous either way.
fn as_ciphertext(polys: [RnsPoly; 2], degree: usize) -> LeanCiphertext {
    LeanCiphertext {
        moduli: FOLD_MODULI.to_vec(),
        degree,
        level: 0,
        variable_time: false,
        polys: polys.to_vec(),
        plain_bound: 1,
    }
}

fn pair_up(polys: Vec<RnsPoly>, degree: usize) -> Vec<LeanCiphertext> {
    let mut iter = polys.into_iter();
    std::iter::from_fn(|| {
        let a = iter.next()?;
        let b = iter.next().expect("even batch");
        Some(as_ciphertext([a, b], degree))
    })
    .collect()
}

fn shape_template(degree: usize) -> LeanCiphertext {
    as_ciphertext([synth_poly(1, degree), synth_poly(2, degree)], degree)
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

fn us(d: Duration) -> f64 {
    d.as_secs_f64() * 1e6
}

// ── PAIR A: NTT -> fold ──────────────────────────────────────────────────────────────────────

/// FUSED: the NTT's output buffer is adopted where it lies and folded. Nothing crosses to the host
/// until the single final download.
fn a_fused(a: &Arena, e: &RnsNttEngine, inputs: &[RnsPoly], degree: usize) -> LeanCiphertext {
    let resident = e
        .forward_odd_batch_resident(inputs, &FOLD_MODULI)
        .expect("resident forward NTT batch");
    let n_cts = inputs.len() / 2;
    let adopted = a.adopt_resident(
        resident.buffer,
        &shape_template(degree),
        n_cts,
        &vec![1u64; n_cts],
        &vec![false; n_cts],
    );
    let folded = a.fold_resident(&adopted);
    a.download(&folded).pop().expect("one folded ciphertext")
}

/// FUSED, but stopping short of the readback — the stage's result stays a handle. The K-sweep
/// needs this: a "fused" pipeline that downloads after every stage pays K synchronizations and is
/// not fused at all, which is precisely the artifact an earlier draft of this binary measured and
/// nearly reported as "compounding does not transfer to this pair".
fn a_fused_resident(
    a: &Arena,
    e: &RnsNttEngine,
    inputs: &[RnsPoly],
    degree: usize,
) -> fhegg_fhe::gpu_arena::ResidentHandle {
    let resident = e
        .forward_odd_batch_resident(inputs, &FOLD_MODULI)
        .expect("resident forward NTT batch");
    let n_cts = inputs.len() / 2;
    let adopted = a.adopt_resident(
        resident.buffer,
        &shape_template(degree),
        n_cts,
        &vec![1u64; n_cts],
        &vec![false; n_cts],
    );
    a.fold_resident(&adopted)
}

/// UNFUSED, stopping short of the FINAL readback — but the NTT's own readback has already happened,
/// which is the whole point: that synchronization is per stage and cannot be amortized.
fn a_unfused_resident(
    a: &Arena,
    e: &RnsNttEngine,
    inputs: &[RnsPoly],
    degree: usize,
) -> fhegg_fhe::gpu_arena::ResidentHandle {
    let transformed = e
        .forward_odd_batch(inputs, &FOLD_MODULI)
        .expect("host-round-trip forward NTT batch");
    let cts = pair_up(transformed.polynomials, degree);
    let uploaded = a.upload(&cts);
    a.fold_resident(&uploaded)
}

/// UNFUSED: what the crate did before today — the NTT reads its batch back to the host as
/// `RnsPoly`s, the host redresses them as ciphertexts, and the arena uploads them again.
fn a_unfused(a: &Arena, e: &RnsNttEngine, inputs: &[RnsPoly], degree: usize) -> LeanCiphertext {
    let transformed = e
        .forward_odd_batch(inputs, &FOLD_MODULI)
        .expect("host-round-trip forward NTT batch");
    let cts = pair_up(transformed.polynomials, degree);
    let uploaded = a.upload(&cts);
    let folded = a.fold_resident(&uploaded);
    a.download(&folded).pop().expect("one folded ciphertext")
}

/// Half of the unfused round trip on its own: the NTT batch down to the host, reassembled into the
/// `RnsPoly`s a caller actually receives.
fn a_ntt_download_only(e: &RnsNttEngine, inputs: &[RnsPoly]) -> usize {
    e.forward_odd_batch(inputs, &FOLD_MODULI)
        .expect("host-round-trip forward NTT batch")
        .polynomials
        .len()
}

// ── PAIR B: NTT -> fold -> bridge -> MLE fold ────────────────────────────────────────────────

/// FUSED: three kernels, two seams, one submission chain, one 4-byte readback.
fn b_fused(
    a: &Arena,
    e: &RnsNttEngine,
    inputs: &[RnsPoly],
    degree: usize,
    challenges: &[u32],
) -> u32 {
    let resident = e
        .forward_odd_batch_resident(inputs, &FOLD_MODULI)
        .expect("resident forward NTT batch");
    let n_cts = inputs.len() / 2;
    let adopted = a.adopt_resident(
        resident.buffer,
        &shape_template(degree),
        n_cts,
        &vec![1u64; n_cts],
        &vec![false; n_cts],
    );
    let folded = a.fold_resident(&adopted);
    let mut table = a.bridge_to_babybear(&folded);
    a.mle_fold_rounds(&mut table, challenges);
    a.download_table(&table)[0]
}

/// UNFUSED: the same three kernels with a host round trip at each of the two seams.
fn b_unfused(
    a: &Arena,
    e: &RnsNttEngine,
    inputs: &[RnsPoly],
    degree: usize,
    table_len: usize,
    challenges: &[u32],
) -> u32 {
    let folded_ct = a_unfused(a, e, inputs, degree);
    let host_table = bridge_lanes_to_babybear(&lanes_of(&folded_ct), table_len);
    let mut table = a.upload_table(&host_table);
    a.mle_fold_rounds(&mut table, challenges);
    a.download_table(&table)[0]
}

// ── the fixed cost, measured rather than assumed ─────────────────────────────────────────────

/// What ONE device synchronization costs when almost no bytes cross. Every raw speedup below sits
/// on top of this; subtracting it is what turns "one fewer stall" into a claim about traffic.
fn sync_floor(a: &Arena, e: &RnsNttEngine) -> Duration {
    let degree = 256;
    let inputs = vec![synth_poly(3, degree), synth_poly(4, degree)];
    let mut times = Vec::with_capacity(REPS);
    for _ in 0..REPS {
        a.wait_idle();
        let t = Instant::now();
        let _ = a_fused(a, e, &inputs, degree);
        times.push(t.elapsed());
        a.clear_pool();
    }
    median(times)
}

fn main() {
    if cfg!(debug_assertions) {
        eprintln!("REFUSED: build with --release. Debug timings measure rustc, not the GPU.");
        std::process::exit(2);
    }
    let Some(a) = arena() else {
        eprintln!("no wgpu adapter — NTT/fold fusion bench cannot run (headless)");
        std::process::exit(1);
    };
    let engine = RnsNttEngine::new();
    if !engine.has_gpu() {
        eprintln!("no wgpu NTT backend — nothing to fuse");
        std::process::exit(1);
    }

    println!("# NTT -> fold fusion, made reachable by the one-device consolidation (gpu_device)");
    match fhegg_fhe::gpu_device::shared_gpu() {
        Ok(gpu) => println!(
            "# adapter: {} [{:?} / {:?}]  max_storage_binding={} max_buffer={}",
            gpu.info.name,
            gpu.info.device_type,
            gpu.info.backend,
            gpu.limits.max_storage_buffer_binding_size,
            gpu.limits.max_buffer_size
        ),
        Err(reason) => println!("# adapter: UNAVAILABLE ({reason})"),
    }
    println!(
        "# ONE shared device serves the NTT pipelines, the fold pipeline and the MLE pipeline."
    );
    println!("# median of {REPS} reps, wall clock including the device wait");

    let floor = sync_floor(&a, &engine);
    println!("#");
    println!(
        "# ⚑ per-synchronization floor (1 poly, degree 256, whole fused chain): {:.1} us",
        us(floor)
    );
    println!("#   FUSED pays one sync; UNFUSED pays two. `traffic` below subtracts exactly that.");
    println!("#");

    // ── PAIR A ───────────────────────────────────────────────────────────────────────────────
    println!("## PAIR A — forward NTT batch -> RNS fold-add");
    println!(
        "# {:>7} {:>5} {:>11} {:>10} {:>10} {:>10} {:>8} {:>8}",
        "degree", "batch", "batch_B", "fused_us", "unfus_us", "nttdl_us", "raw", "traffic"
    );
    for &(degree, batch) in CASES {
        let inputs: Vec<_> = (0..batch)
            .map(|i| synth_poly(0x5EED ^ (i as u64 + 1), degree))
            .collect();
        let batch_bytes = batch * FOLD_MODULI.len() * degree * 8;

        // Parity, every size. If these disagree the columns below time two different computations.
        let f = a_fused(&a, &engine, &inputs, degree);
        let u = a_unfused(&a, &engine, &inputs, degree);
        assert_eq!(
            f, u,
            "degree {degree}: fused and unfused NTT->fold disagree — the measurement is void"
        );
        a.clear_pool();

        let mut ft = Vec::with_capacity(REPS);
        let mut ut = Vec::with_capacity(REPS);
        let mut dt = Vec::with_capacity(REPS);
        for _ in 0..REPS {
            a.wait_idle();
            let t = Instant::now();
            std::hint::black_box(a_fused(&a, &engine, &inputs, degree));
            ft.push(t.elapsed());
            a.clear_pool();

            a.wait_idle();
            let t = Instant::now();
            std::hint::black_box(a_unfused(&a, &engine, &inputs, degree));
            ut.push(t.elapsed());
            a.clear_pool();

            a.wait_idle();
            let t = Instant::now();
            std::hint::black_box(a_ntt_download_only(&engine, &inputs));
            dt.push(t.elapsed());
        }
        let (fm, um, dm) = (median(ft), median(ut), median(dt));
        let raw = us(um) / us(fm);
        let traffic = traffic_ratio(us(fm), us(um), us(floor));
        println!(
            "  {:>7} {:>5} {:>11} {:>10.1} {:>10.1} {:>10.1} {:>7.2}x {:>8}",
            degree,
            batch,
            batch_bytes,
            us(fm),
            us(um),
            us(dm),
            raw,
            show(traffic)
        );
    }

    // ── PAIR B ───────────────────────────────────────────────────────────────────────────────
    println!();
    println!("## PAIR B — forward NTT batch -> fold -> BabyBear bridge -> MLE fold (3 kernels)");
    println!(
        "# {:>7} {:>5} {:>11} {:>10} {:>10} {:>6} {:>8} {:>8}",
        "degree", "batch", "table_len", "fused_us", "unfus_us", "vars", "raw", "traffic"
    );
    for &(degree, batch) in CASES {
        let inputs: Vec<_> = (0..batch)
            .map(|i| synth_poly(0x5EED ^ (i as u64 + 1), degree))
            .collect();
        // The folded ciphertext is a poly PAIR: 2 x 3 RNS rows x degree lanes.
        let lanes = 2 * FOLD_MODULI.len() * degree;
        let table_len = table_len_for_lanes(lanes);
        let n_vars = table_len.trailing_zeros() as usize;
        let challenges = fixture_challenges(n_vars, 0xF05E ^ degree as u64);

        let f = b_fused(&a, &engine, &inputs, degree, &challenges);
        let u = b_unfused(&a, &engine, &inputs, degree, table_len, &challenges);
        assert_eq!(
            f, u,
            "degree {degree}: fused and unfused NTT->fold->MLE disagree — the measurement is void"
        );
        a.clear_pool();

        let mut ft = Vec::with_capacity(REPS);
        let mut ut = Vec::with_capacity(REPS);
        for _ in 0..REPS {
            a.wait_idle();
            let t = Instant::now();
            std::hint::black_box(b_fused(&a, &engine, &inputs, degree, &challenges));
            ft.push(t.elapsed());
            a.clear_pool();

            a.wait_idle();
            let t = Instant::now();
            std::hint::black_box(b_unfused(
                &a,
                &engine,
                &inputs,
                degree,
                table_len,
                &challenges,
            ));
            ut.push(t.elapsed());
            a.clear_pool();
        }
        let (fm, um) = (median(ft), median(ut));
        let raw = us(um) / us(fm);
        let traffic = traffic_ratio(us(fm), us(um), us(floor));
        println!(
            "  {:>7} {:>5} {:>11} {:>10.1} {:>10.1} {:>6} {:>7.2}x {:>8}",
            degree,
            batch,
            table_len,
            us(fm),
            us(um),
            n_vars,
            raw,
            show(traffic)
        );
    }

    // ── the compounding result ───────────────────────────────────────────────────────────────
    println!();
    println!("## K STAGES — the robust shape: fused pays ONE sync for K stages, unfused pays K+1");
    println!(
        "#   Nothing is read back inside the fused loop; the single download at the end waits"
    );
    println!(
        "#   on the whole queue, so all K stages' work is included in the one synchronization."
    );
    let degree = 4096;
    println!("# degree {degree}, batch {STAGE_BATCH} polys; per-stage microseconds");
    println!(
        "# {:>3} {:>14} {:>16} {:>8}",
        "K", "fused/stage", "unfused/stage", "ratio"
    );
    for &k in STAGE_COUNTS {
        let stages: Vec<Vec<RnsPoly>> = (0..k)
            .map(|s| {
                (0..STAGE_BATCH)
                    .map(|i| synth_poly(0xC0DE ^ ((s * STAGE_BATCH + i) as u64 + 1), degree))
                    .collect()
            })
            .collect();

        let mut ft = Vec::with_capacity(REPS);
        let mut ut = Vec::with_capacity(REPS);
        for _ in 0..REPS {
            // FUSED: K stages, NOTHING read back until the end. One synchronization for all K.
            a.wait_idle();
            let t = Instant::now();
            let mut last = None;
            for stage in &stages {
                last = Some(a_fused_resident(&a, &engine, stage, degree));
            }
            // The single sync. One device and one queue, so waiting on this handle waits on every
            // stage's work — which is exactly the property being measured.
            std::hint::black_box(a.download(&last.expect("at least one stage")).len());
            ft.push(t.elapsed());
            a.clear_pool();

            // UNFUSED: each stage's NTT reads back to the host before the fold can have it, so the
            // synchronization is per stage and there are K of them plus the final one.
            a.wait_idle();
            let t = Instant::now();
            let mut last = None;
            for stage in &stages {
                last = Some(a_unfused_resident(&a, &engine, stage, degree));
            }
            std::hint::black_box(a.download(&last.expect("at least one stage")).len());
            ut.push(t.elapsed());
            a.clear_pool();
        }
        let fps = us(median(ft)) / k as f64;
        let ups = us(median(ut)) / k as f64;
        println!("  {:>3} {:>14.1} {:>16.1} {:>7.2}x", k, fps, ups, ups / fps);
    }

    println!();
    println!("# ⚠ Unified memory: every figure above is a LOWER BOUND on discrete/FPGA silicon.");
    println!(
        "# ⚠ `raw` includes one fewer synchronization; `traffic` removes it. Carry `traffic`."
    );
    println!(
        "# ⚠ `traffic` is BLANK where both arms sit within {FLOOR_HEADROOM:.0}x of the sync floor: \
there the subtraction is two large noisy numbers and its quotient means nothing."
    );
}
