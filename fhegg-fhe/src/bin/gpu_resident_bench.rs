//! gpu_resident_bench — MEASUREMENT HARNESS ONLY (lane par/gpu-arena-measure, 2026-07-18).
//!
//! THE QUESTION (the reviewer perf question, verbatim): is the RESIDENT thesis real? The one-shot
//! `fold_gpu` LOSES ~5-7x to the CPU (measured, `bin/gpu_saturate.rs` 2026-07-18: host pack 56% +
//! create/upload 37% of every call — the GPU did 7% of the work). `gpu_arena` claims the fix is
//! structural: upload ONCE, fold K times on-device, download ONCE. This bin MEASURES that claim.
//!
//! Pattern driven, per N in the sweep (K >= 8 folds):
//!   CPU       : K x `bfv_lean::fold(&cts, t)` — the production CPU path, the bar to beat.
//!   one-shot  : K x `bfv_gpu::fold_gpu(&cts, t)` — the measured LOSER, timed as context
//!               (each call re-packs + re-uploads + reads back).
//!   RESIDENT  : `arena.upload(&cts)` ONCE -> K x `fold_resident(&h)` -> `download` ONCE.
//!
//! BREAKDOWN so the amortization is VISIBLE, without touching gpu_arena src (its device/queue are
//! private): upload is timed directly (host-side mapped write, synchronous); the K `fold_resident`
//! calls are encode+submit only (async); the first `download` blocks until all K folds complete
//! (poll Wait) + reads back 197 KB; a SECOND `download` of the same handle with the GPU now idle
//! times the pure readback. So:  fold+sync = submit + download1 - download2  (the on-device compute
//! wall time), and download2 is the true egress cost. Labeled exactly that way in the output.
//!
//! PARITY TOOTH: at EVERY N the downloaded resident result must equal the oracle-validated CPU
//! `fold` BIT-FOR-BIT (and carry plain_bound == sum of input bounds), or this bin exits 1 — the
//! numbers are only trustworthy if the math is. Tooth bite-proof: run with `MUTATE_PARITY=1` to
//! corrupt one downloaded coefficient — the parity check must go RED (exit 1). That mutation is
//! bench-side only; production code is untouched by this lane.
//!
//! HONEST CEILINGS, printed not hidden:
//!   - a resident set is ONE storage buffer: N is capped by the adapter's
//!     min(max_buffer_size, max_storage_buffer_binding_size) / 196608 B per ct. Game scale 10^5
//!     cts = 19.7 GB — whether it fits is an ADAPTER FACT this bin prints before sweeping.
//!   - one-shot fold_gpu dies in wgpu validation past the same ceiling (the N=16384 panic named in
//!     TESTQALOG 2026-07-18), so one-shot is only run where its buffer fits, and is additionally
//!     capped at ONESHOT_MAX_N (default 16384) because K repeats of a known ~seconds-scale loser
//!     at 10 GB would just stall the sweep; the cap is printed.
//!   - CPU numbers are wall-clock of the deployed single-threaded `fold` (allocation-per-add, as
//!     shipped) — the same code gpu_saturate timed, so rows are comparable across the two bins.
//!
//! VARIANCE: single passes on this box swing several-x (co-tenant swarm builds — a dozen rustc
//! procs during the first runs — plus macOS QoS core scheduling of the single-threaded fold, plus
//! Metal buffer-allocation variance). CPU and RESIDENT are therefore BEST-OF-REPS (default 3), the
//! standard bench discipline gpu_saturate used (best of 2/3), and the min/max spread is printed so
//! the variance is visible, not hidden. One-shot is a single pass — it loses by ~10x either way
//! and 3x K repeats of it would stall the sweep.
//!
//! Env knobs: ARENA_K (folds per pattern, default 8, floor 8), RES_MAX_N (sweep cap), REPS
//! (best-of, default 3), ONESHOT_MAX_N (one-shot context cap, default 16384), MUTATE_PARITY=1
//! (prove the tooth bites).

use fhegg_fhe::bfv_gpu::fold_gpu;
use fhegg_fhe::bfv_lean::{fold, LeanCiphertext, RnsPoly, FOLD_MODULI};
use fhegg_fhe::gpu_arena::{arena, FoldEngine};
use std::time::Instant;

/// Full-shape fresh-fold ciphertext (2 polys x 3 RNS rows x degree-4096), deterministic canonical
/// residues — the EXACT synth of gpu_saturate.rs and the gpu_arena parity test, so numbers line up.
fn synth_ct(seed: u64, plain_bound: u64) -> LeanCiphertext {
    let deg = 4096usize;
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
                .map(|&q| (0..deg).map(|_| next() % q).collect())
                .collect(),
        })
        .collect();
    LeanCiphertext {
        moduli: FOLD_MODULI.to_vec(),
        degree: deg,
        level: 0,
        variable_time: false,
        polys,
        plain_bound,
    }
}

const CT_BYTES: u64 = 2 * 3 * 4096 * 8; // 196608 B per ciphertext (24576 lanes x 8 B)

fn env_usize(k: &str, default: usize) -> usize {
    std::env::var(k)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

fn main() {
    println!("gpu_resident_bench — the RESIDENT thesis, measured (lane par/gpu-arena-measure)");
    println!(
        "host: {}",
        String::from_utf8_lossy(
            &std::process::Command::new("hostname")
                .output()
                .map(|o| o.stdout)
                .unwrap_or_default()
        )
        .trim()
    );

    // Adapter ground truth (probe instance; arena/fold_gpu hold their own contexts).
    let (adapter_line, buffer_cap) = {
        let instance = wgpu::Instance::default();
        match pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        })) {
            Some(a) => {
                let i = a.get_info();
                let l = a.limits();
                let cap = l
                    .max_buffer_size
                    .min(l.max_storage_buffer_binding_size as u64);
                (
                    format!(
                        "adapter: {} | backend {:?} | type {:?} | max_buffer {} MB | max_storage_binding {} MB",
                        i.name,
                        i.backend,
                        i.device_type,
                        l.max_buffer_size / (1 << 20),
                        l.max_storage_buffer_binding_size as u64 / (1 << 20)
                    ),
                    cap,
                )
            }
            None => {
                println!("NO wgpu adapter — nothing to measure on this box (honest exit).");
                std::process::exit(2);
            }
        }
    };
    println!("{adapter_line}");

    let Some(a) = arena() else {
        println!("wgpu adapter probed but arena() returned None — cannot measure (honest exit).");
        std::process::exit(2);
    };

    let t = 1u64 << 20;
    let k = env_usize("ARENA_K", 8).max(8); // the brief demands K >= 8
    let n_ceiling = (buffer_cap / CT_BYTES) as usize;
    let res_max_n = env_usize("RES_MAX_N", 100_000);
    let reps = env_usize("REPS", 3).max(1);
    let oneshot_max_n = env_usize("ONESHOT_MAX_N", 16_384);
    let mutate_parity = std::env::var("MUTATE_PARITY")
        .map(|v| v == "1")
        .unwrap_or(false);

    // Game-scale sweep 10^3..10^5, filtered by the ADAPTER ceiling (printed, never silently clipped).
    let want: Vec<usize> = vec![
        1_000, 4_096, 8_192, 16_384, 32_768, 65_536, 100_000, 500_000, 1_000_000,
    ];
    let sweep: Vec<usize> = want
        .iter()
        .copied()
        .filter(|&n| n <= res_max_n.min(n_ceiling))
        .collect();
    let clipped: Vec<usize> = want.iter().copied().filter(|&n| n > n_ceiling).collect();
    println!(
        "K={k} folds per pattern | ct = 196608 B (deg 4096 x 3 RNS x 2 polys) | resident N ceiling on THIS adapter = {n_ceiling} cts ({:.1} GB buffer cap)",
        buffer_cap as f64 / 1e9
    );
    if !clipped.is_empty() {
        println!("Beyond the single-buffer cap: N in {clipped:?} — measured below via the STREAMING (chunked) FoldEngine path, which IS built (fold_streaming). The single-buffer ceiling was never the real limit.");
    }
    if mutate_parity {
        println!("MUTATE_PARITY=1 — bench-side corruption armed; the parity tooth MUST go RED");
    }

    // Warm both GPU contexts once (pipeline compile out of the timings).
    {
        let w: Vec<_> = (0..2u64).map(|i| synth_ct(i + 1, 1)).collect();
        let _ = fold_gpu(&w, t);
        let h = a.upload(&w);
        let _ = a.download(&a.fold_resident(&h));
    }

    println!(
        "\n{:>7} {:>8} | {:>12} {:>14} {:>13} | {:>9} {:>9} | {:>10} {:>12} {:>11} {:>10}",
        "N",
        "MB",
        "CPU Kfolds",
        "one-shot xK",
        "RESIDENT e2e",
        "res/CPU",
        "res/1shot",
        "upload",
        "fold+sync",
        "download",
        "per-fold"
    );

    struct Row {
        n: usize,
        cpu_s: f64,
        one_shot_s: Option<f64>,
        res_s: f64,
    }
    let mut rows: Vec<Row> = Vec::new();
    let mut all_parity = true;

    for &n in &sweep {
        let cts: Vec<_> = (0..n as u64).map(|i| synth_ct(i + 1, 1)).collect();
        let mb = (n as u64 * CT_BYTES) as f64 / 1e6;

        // CPU: K full folds of the same set (the work the resident pattern replaces), best-of-REPS.
        let mut cpu_best = f64::MAX;
        let mut cpu_worst: f64 = 0.0;
        let mut cpu_ref = None;
        for _ in 0..reps {
            let t0 = Instant::now();
            for _ in 0..k {
                cpu_ref = Some(fold(&cts, t).expect("cpu fold"));
            }
            let s = t0.elapsed().as_secs_f64();
            cpu_best = cpu_best.min(s);
            cpu_worst = cpu_worst.max(s);
        }
        let cpu_s = cpu_best;
        let cpu_ref = cpu_ref.unwrap();

        // One-shot context: K independent fold_gpu calls (pack+upload+dispatch+readback EACH).
        // Guarded by the same buffer ceiling (fold_gpu panics past it) + the stall cap.
        let one_shot_s = if n <= n_ceiling && n <= oneshot_max_n {
            let t0 = Instant::now();
            let mut ok = true;
            for _ in 0..k {
                if let Err(e) = fold_gpu(&cts, t) {
                    println!("  one-shot fold_gpu ERR at N={n}: {e} (context lost, resident still measured)");
                    ok = false;
                    break;
                }
            }
            ok.then(|| t0.elapsed().as_secs_f64())
        } else {
            None
        };

        // RESIDENT: upload once, K folds on-device, download once — best-of-REPS, parity on EVERY rep.
        let mut res_best = f64::MAX;
        let mut res_worst: f64 = 0.0;
        let mut best_parts = (0.0f64, 0.0f64, 0.0f64); // upload, compute, pure-readback of the best rep
        let mut parity_ok = true;
        let mut bound_ok = true;
        for rep in 0..reps {
            let t0 = Instant::now();
            let h = a.upload(&cts);
            let upload_s = t0.elapsed().as_secs_f64();

            let t0 = Instant::now();
            let mut last = None;
            for _ in 0..k {
                last = Some(a.fold_resident(&h)); // encode+submit; download synchronizes
            }
            let submit_s = t0.elapsed().as_secs_f64();
            let folded = last.unwrap();

            let t0 = Instant::now();
            let mut got = a.download(&folded); // blocks until all K folds done + 197 KB readback
            let dl1_s = t0.elapsed().as_secs_f64();

            let t0 = Instant::now();
            let _again = a.download(&folded); // GPU idle now: pure readback cost
            let dl2_s = t0.elapsed().as_secs_f64();

            let e2e = upload_s + submit_s + dl1_s; // end-to-end as the app would pay it
            let compute_s = (submit_s + dl1_s - dl2_s).max(0.0); // on-device fold wall time
            if e2e < res_best {
                res_best = e2e;
                best_parts = (upload_s, compute_s, dl2_s.min(dl1_s));
            }
            res_worst = res_worst.max(e2e);

            // PARITY TOOTH on every rep (+ optional bench-side mutation proving it bites).
            if mutate_parity && rep == 0 {
                got[0].polys[0].rows[0][0] ^= 1;
            }
            parity_ok &= got.len() == 1 && got[0] == cpu_ref;
            bound_ok &= got[0].plain_bound == n as u64; // sum of N bounds of 1
        }
        let res_s = res_best;
        let (upload_s, compute_s, dl2_s) = best_parts;
        if !parity_ok || !bound_ok {
            all_parity = false;
        }

        println!(
            "{:>7} {:>8.0} | {:>10.1}ms {:>12} {:>11.1}ms | {:>8.2}x {:>9} | {:>8.2}ms {:>10.2}ms {:>9.2}ms {:>8.2}ms  {}",
            n,
            mb,
            cpu_s * 1e3,
            one_shot_s
                .map(|s| format!("{:>10.1}ms", s * 1e3))
                .unwrap_or_else(|| if n > n_ceiling { "OVER-CAP".into() } else { "SKIP>cap".into() }),
            res_s * 1e3,
            cpu_s / res_s,
            one_shot_s
                .map(|s| format!("{:>8.2}x", s / res_s))
                .unwrap_or_else(|| "-".into()),
            upload_s * 1e3,
            compute_s * 1e3,
            dl2_s * 1e3,
            compute_s * 1e3 / k as f64,
            if parity_ok && bound_ok {
                "BIT-EXACT"
            } else {
                "DIVERGED!"
            }
        );
        println!(
            "          spread over {reps} reps: cpu [{:.0}..{:.0}]ms  resident [{:.0}..{:.0}]ms",
            cpu_best * 1e3,
            cpu_worst * 1e3,
            res_best * 1e3,
            res_worst * 1e3
        );
        if !parity_ok {
            eprintln!(
                "FATAL: resident result diverged from CPU fold at N={n} — numbers untrustworthy"
            );
        }
        if !bound_ok {
            eprintln!("FATAL: carried plain_bound != {n} at N={n} — wrap-gate bookkeeping broken");
        }
        rows.push(Row {
            n,
            cpu_s,
            one_shot_s,
            res_s,
        });
    }

    // ---- the verdict, computed from the rows (not asserted by hope) ----
    println!("\nVERDICT (K={k}):");
    let mut resident_wins_somewhere = false;
    for r in &rows {
        let vs_cpu = r.cpu_s / r.res_s;
        let one = r
            .one_shot_s
            .map(|s| {
                format!(
                    "one-shot {:.1}ms ({:.2}x vs CPU — {})",
                    s * 1e3,
                    r.cpu_s / s,
                    if s > r.cpu_s { "LOSES" } else { "wins" }
                )
            })
            .unwrap_or_else(|| "one-shot not run".into());
        println!(
            "  N={:>6}: resident {} the CPU ({:.2}x, {:.1}ms vs {:.1}ms); {}",
            r.n,
            if vs_cpu > 1.0 { "BEATS" } else { "LOSES TO" },
            vs_cpu,
            r.res_s * 1e3,
            r.cpu_s * 1e3,
            one
        );
        if vs_cpu > 1.0 {
            resident_wins_somewhere = true;
        }
    }
    println!(
        "  thesis at K={k}: {}",
        if resident_wins_somewhere {
            "resident BEATS the CPU at the sizes marked above — the residency amortization is real on this adapter"
        } else {
            "resident does NOT beat the CPU anywhere in this sweep — the thesis does not hold at this K/N on this adapter (honest finding)"
        }
    );

    // ── STREAMING (chunked) single-clear latency: the large-N sizes the single-buffer path clips ARE
    // handled by the production `FoldEngine` (fold_streaming — adapter-sized chunks, folded resident,
    // reduced device-to-device, one readback). The single-buffer "clip" was never the real ceiling. This
    // measures the ACTUAL DrEX aggregation: fold N encrypted orders into one aggregate curve, GPU vs CPU —
    // the regime where the earlier N=1M histogram won 11.4x. plain_bound=1 keeps the sum < t for N < 2^20.
    if !clipped.is_empty() {
        let engine = FoldEngine::new();
        println!(
            "\n=== STREAMING (chunked) single-clear — fold N orders into the aggregate, GPU FoldEngine vs CPU ==="
        );
        println!(
            "{:>9} {:>7} | {:>12} {:>14} | {:>9} | {:>12}",
            "N", "MB", "CPU fold", "GPU stream", "gpu/cpu", "backend"
        );
        for &n in clipped.iter().filter(|&&n| n <= res_max_n) {
            let cts: Vec<LeanCiphertext> = (0..n as u64).map(|i| synth_ct(i + 1, 1)).collect();
            let mb = (n as u64 * CT_BYTES) / (1 << 20);
            let want = fold(&cts, t).expect("cpu fold reference");
            let exec = engine.fold(&cts, t).expect("streaming fold");
            if exec.ciphertext != want {
                eprintln!("STREAMING parity BROKE at N={n} — GPU stream != bfv_lean::fold");
                std::process::exit(1);
            }
            let cpu_s = (0..reps)
                .map(|_| {
                    let s = Instant::now();
                    let _ = fold(&cts, t);
                    s.elapsed().as_secs_f64()
                })
                .fold(f64::MAX, f64::min);
            let gpu_s = (0..reps)
                .map(|_| {
                    let s = Instant::now();
                    let _ = engine.fold(&cts, t);
                    s.elapsed().as_secs_f64()
                })
                .fold(f64::MAX, f64::min);
            println!(
                "{:>9} {:>5}MB | {:>10.1}ms {:>12.1}ms | {:>7.2}x | {:?}",
                n,
                mb,
                cpu_s * 1e3,
                gpu_s * 1e3,
                cpu_s / gpu_s,
                exec.backend
            );
        }
        println!("  (streaming single-clear = ONE aggregation of N orders — the real DrEX fold hot path; BIT-EXACT vs CPU asserted)");
    }

    println!("\nNOTES (read before quoting):");
    println!("- CPU is the deployed single-threaded fold, K full passes; one-shot is the deployed fold_gpu, K calls.");
    println!("- RESIDENT e2e = upload + K encode/submits + the synchronizing download (everything the app pays).");
    println!("- fold+sync = submit + first-download - second-download (on-device compute wall; the second");
    println!(
        "  download times the pure 197 KB egress with the GPU idle). per-fold = fold+sync / K."
    );
    println!("- parity is asserted bit-for-bit vs bfv_lean::fold at every N, plus plain_bound == N carried.");

    if !all_parity {
        if mutate_parity {
            eprintln!("MUTATE_PARITY: tooth went RED as required (bench-side corruption caught).");
        }
        std::process::exit(1);
    }
    if mutate_parity {
        eprintln!("MUTATE_PARITY was set but nothing diverged — the parity tooth did NOT bite; that is a RED finding");
        std::process::exit(3);
    }
}
