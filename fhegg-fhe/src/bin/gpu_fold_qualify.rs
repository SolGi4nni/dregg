//! Machine-readable CPU-versus-wgpu qualification for the production BFV
//! additive fold.
//!
//! This measures a *single complete call on a retained `FoldEngine`*: validation,
//! upload, resident dispatch, synchronization, and readback. Adapter/device/
//! pipeline construction is outside the timing. The CPU baseline is the direct
//! [`fhegg_fhe::bfv_lean::fold`] arithmetic path. This is deliberately distinct
//! from `gpu_resident_bench`, which studies an upload-once / repeated on-device
//! workload. A GPU threshold learned here must not be applied to that different
//! workload (or vice versa).
//!
//! Environment:
//! - `FHEGG_GPU_QUALIFY_NS=1,2,4,...` sampled batch sizes (default through 512)
//! - `FHEGG_GPU_QUALIFY_REPS=5` timed repetitions per size
//! - `FHEGG_GPU_QUALIFY_MARGIN_BPS=500` required win margin (500 = 5%)
//! - `FHEGG_GPU_QUALIFY_REQUIRE_GPU=1` fail if no sample actually dispatched
//!   through wgpu
//!
//! A crossover is reported only after two consecutive sampled sizes beat the
//! CPU median by the configured margin. That is a measurement rule, not an
//! automatic production dispatch policy.

use std::hint::black_box;
use std::time::Instant;

use fhegg_fhe::bfv_lean::{fold, LeanCiphertext, RnsPoly, FOLD_MODULI};
use fhegg_fhe::gpu_qualification::{BfvFoldDispatch, DiagnosedFoldEngine, WgpuAdapterStatus};
use serde::Serialize;

const DEFAULT_SIZES: &[usize] = &[1, 2, 4, 8, 16, 32, 64, 128, 256, 512];
const DEGREE: usize = 4096;
const PLAINTEXT_MODULUS: u64 = 1u64 << 40;

#[derive(Clone, Debug, Serialize)]
struct QualificationSettings {
    batch_sizes: Vec<usize>,
    repetitions: usize,
    win_margin_basis_points: u32,
    confirmation_samples: usize,
    plaintext_modulus: u64,
    require_gpu: bool,
    measurement_scope: &'static str,
    cpu_baseline: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct QualificationSample {
    input_ciphertexts: usize,
    input_bytes: u64,
    cpu_median_ns: u64,
    cpu_min_ns: u64,
    selected_backend_median_ns: u64,
    selected_backend_min_ns: u64,
    /// Present only when every measured selected-backend execution was an
    /// actual resident wgpu dispatch.
    gpu_median_ns: Option<u64>,
    cpu_over_gpu_speedup: Option<f64>,
    dispatch: BfvFoldDispatch,
    dispatch_stable: bool,
    bit_exact: bool,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "status", rename_all = "snake_case")]
enum CrossoverFinding {
    Confirmed {
        first_sample_n: usize,
        next_sample_n: usize,
        required_margin_basis_points: u32,
    },
    NotObserved {
        required_margin_basis_points: u32,
    },
    NoGpuDispatch,
}

#[derive(Clone, Debug, Serialize)]
struct QualificationReport {
    report: &'static str,
    host: String,
    adapter: WgpuAdapterStatus,
    gpu_arena_ready: bool,
    settings: QualificationSettings,
    samples: Vec<QualificationSample>,
    crossover: CrossoverFinding,
    all_bit_exact: bool,
}

fn synth_ct(seed: u64) -> LeanCiphertext {
    let mut state = seed;
    let mut next = || {
        state = state
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .rotate_left(17)
            .wrapping_add(1);
        state
    };
    let polys = (0..2)
        .map(|_| RnsPoly {
            rows: FOLD_MODULI
                .iter()
                .map(|&modulus| (0..DEGREE).map(|_| next() % modulus).collect())
                .collect(),
        })
        .collect();
    LeanCiphertext {
        moduli: FOLD_MODULI.to_vec(),
        degree: DEGREE,
        level: 0,
        variable_time: false,
        polys,
        plain_bound: 1,
    }
}

fn ciphertext_bytes(ciphertext: &LeanCiphertext) -> Result<u64, String> {
    let coefficients = ciphertext
        .polys
        .iter()
        .flat_map(|poly| &poly.rows)
        .try_fold(0usize, |total, row| total.checked_add(row.len()))
        .ok_or_else(|| "ciphertext coefficient count overflow".to_owned())?;
    u64::try_from(coefficients)
        .ok()
        .and_then(|count| count.checked_mul(8))
        .ok_or_else(|| "ciphertext byte count overflow".to_owned())
}

fn parse_sizes() -> Result<Vec<usize>, String> {
    let Some(raw) = std::env::var("FHEGG_GPU_QUALIFY_NS").ok() else {
        return Ok(DEFAULT_SIZES.to_vec());
    };
    let mut sizes = raw
        .split(',')
        .map(|part| {
            part.trim()
                .parse::<usize>()
                .map_err(|_| format!("invalid batch size {part:?}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    sizes.sort_unstable();
    sizes.dedup();
    if sizes.is_empty() || sizes[0] == 0 {
        return Err("batch sizes must be nonempty positive integers".to_owned());
    }
    let largest_batch = u128::try_from(sizes.last().copied().unwrap_or_default())
        .map_err(|_| "largest batch cannot be represented as u128".to_owned())?;
    if largest_batch >= u128::from(PLAINTEXT_MODULUS) {
        return Err("largest batch exhausts the plaintext wrap budget".to_owned());
    }
    Ok(sizes)
}

fn env_usize(name: &str, default: usize) -> Result<usize, String> {
    match std::env::var(name) {
        Ok(raw) => raw
            .parse::<usize>()
            .map_err(|_| format!("{name} must be a positive integer"))
            .and_then(|value| {
                (value > 0)
                    .then_some(value)
                    .ok_or_else(|| format!("{name} must be positive"))
            }),
        Err(_) => Ok(default),
    }
}

fn env_u32(name: &str, default: u32) -> Result<u32, String> {
    match std::env::var(name) {
        Ok(raw) => raw
            .parse::<u32>()
            .map_err(|_| format!("{name} must be an unsigned integer")),
        Err(_) => Ok(default),
    }
}

fn env_bool(name: &str) -> bool {
    matches!(
        std::env::var(name)
            .unwrap_or_default()
            .trim()
            .to_ascii_lowercase()
            .as_str(),
        "1" | "true" | "yes" | "on"
    )
}

fn elapsed_ns(start: Instant) -> u64 {
    u64::try_from(start.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

fn median(values: &mut [u64]) -> u64 {
    values.sort_unstable();
    values[values.len() / 2]
}

fn host_label() -> String {
    std::env::var("HOSTNAME")
        .ok()
        .filter(|value| !value.trim().is_empty())
        .or_else(|| {
            std::fs::read_to_string("/etc/hostname")
                .ok()
                .map(|value| value.trim().to_owned())
                .filter(|value| !value.is_empty())
        })
        .unwrap_or_else(|| "unknown".to_owned())
}

fn find_crossover(samples: &[QualificationSample], margin_bps: u32) -> CrossoverFinding {
    if !samples.iter().any(|sample| sample.gpu_median_ns.is_some()) {
        return CrossoverFinding::NoGpuDispatch;
    }
    let required = 1.0 + f64::from(margin_bps) / 10_000.0;
    for window in samples.windows(2) {
        let [first, second] = window else {
            unreachable!("windows(2) has exactly two elements")
        };
        if first
            .cpu_over_gpu_speedup
            .is_some_and(|value| value >= required)
            && second
                .cpu_over_gpu_speedup
                .is_some_and(|value| value >= required)
        {
            return CrossoverFinding::Confirmed {
                first_sample_n: first.input_ciphertexts,
                next_sample_n: second.input_ciphertexts,
                required_margin_basis_points: margin_bps,
            };
        }
    }
    CrossoverFinding::NotObserved {
        required_margin_basis_points: margin_bps,
    }
}

fn run() -> Result<(QualificationReport, bool), String> {
    let settings = QualificationSettings {
        batch_sizes: parse_sizes()?,
        repetitions: env_usize("FHEGG_GPU_QUALIFY_REPS", 5)?,
        win_margin_basis_points: env_u32("FHEGG_GPU_QUALIFY_MARGIN_BPS", 500)?,
        confirmation_samples: 2,
        plaintext_modulus: PLAINTEXT_MODULUS,
        require_gpu: env_bool("FHEGG_GPU_QUALIFY_REQUIRE_GPU"),
        measurement_scope:
            "one retained-engine FoldEngine call: preflight + upload + dispatch + wait + readback",
        cpu_baseline: "direct bfv_lean::fold arithmetic path",
    };
    let engine = DiagnosedFoldEngine::auto();
    let adapter = engine.adapter_status().clone();
    let gpu_arena_ready = engine.has_gpu_arena();
    let mut samples = Vec::with_capacity(settings.batch_sizes.len());

    for &n in &settings.batch_sizes {
        let n_u64 = u64::try_from(n)
            .map_err(|_| format!("batch size N={n} cannot be represented as u64"))?;
        let ciphertexts = (0..n_u64)
            .map(|index| synth_ct(index + 1))
            .collect::<Vec<_>>();
        let input_bytes = ciphertext_bytes(&ciphertexts[0])?
            .checked_mul(n_u64)
            .ok_or_else(|| "batch byte count overflow".to_owned())?;

        // Warm CPU caches and the wgpu pipeline outside every timed sample.
        let cpu_warm = fold(&ciphertexts, PLAINTEXT_MODULUS)
            .map_err(|error| format!("CPU warmup at N={n}: {error}"))?;
        let selected_warm = engine
            .fold(&ciphertexts, PLAINTEXT_MODULUS)
            .map_err(|error| format!("selected-backend warmup at N={n}: {error}"))?;
        let mut bit_exact = selected_warm.ciphertext == cpu_warm;
        let dispatch = selected_warm.dispatch;

        let mut cpu_times = Vec::with_capacity(settings.repetitions);
        let mut selected_times = Vec::with_capacity(settings.repetitions);
        let mut dispatch_stable = true;
        for repetition in 0..settings.repetitions {
            // Alternate order so a systematic first-run thermal/cache advantage
            // is not assigned to one backend for every repetition.
            if repetition % 2 == 0 {
                let start = Instant::now();
                let cpu = fold(&ciphertexts, PLAINTEXT_MODULUS)
                    .map_err(|error| format!("CPU timed fold at N={n}: {error}"))?;
                cpu_times.push(elapsed_ns(start));
                black_box(&cpu);

                let start = Instant::now();
                let selected = engine
                    .fold(&ciphertexts, PLAINTEXT_MODULUS)
                    .map_err(|error| format!("selected timed fold at N={n}: {error}"))?;
                selected_times.push(elapsed_ns(start));
                dispatch_stable &= selected.dispatch == dispatch;
                bit_exact &= selected.ciphertext == cpu;
                black_box(&selected.ciphertext);
            } else {
                let start = Instant::now();
                let selected = engine
                    .fold(&ciphertexts, PLAINTEXT_MODULUS)
                    .map_err(|error| format!("selected timed fold at N={n}: {error}"))?;
                selected_times.push(elapsed_ns(start));
                dispatch_stable &= selected.dispatch == dispatch;
                black_box(&selected.ciphertext);

                let start = Instant::now();
                let cpu = fold(&ciphertexts, PLAINTEXT_MODULUS)
                    .map_err(|error| format!("CPU timed fold at N={n}: {error}"))?;
                cpu_times.push(elapsed_ns(start));
                bit_exact &= selected.ciphertext == cpu;
                black_box(&cpu);
            }
        }

        let cpu_min_ns = *cpu_times.iter().min().expect("positive repetitions");
        let selected_backend_min_ns = *selected_times.iter().min().expect("positive repetitions");
        let cpu_median_ns = median(&mut cpu_times);
        let selected_backend_median_ns = median(&mut selected_times);
        let actual_gpu =
            matches!(&dispatch, BfvFoldDispatch::GpuResident { .. }) && dispatch_stable;
        let gpu_median_ns = actual_gpu.then_some(selected_backend_median_ns);
        // A zero-duration observation is below the timer's resolution, not an
        // infinite measured speedup. Leave the ratio absent so the JSON stays
        // standards-compliant and crossover detection remains conservative.
        let cpu_over_gpu_speedup = gpu_median_ns
            .filter(|&gpu_ns| gpu_ns != 0)
            .map(|gpu_ns| cpu_median_ns as f64 / gpu_ns as f64);
        samples.push(QualificationSample {
            input_ciphertexts: n,
            input_bytes,
            cpu_median_ns,
            cpu_min_ns,
            selected_backend_median_ns,
            selected_backend_min_ns,
            gpu_median_ns,
            cpu_over_gpu_speedup,
            dispatch,
            dispatch_stable,
            bit_exact,
        });
    }

    let crossover = find_crossover(&samples, settings.win_margin_basis_points);
    let all_bit_exact = samples.iter().all(|sample| sample.bit_exact);
    let saw_gpu = samples.iter().any(|sample| sample.gpu_median_ns.is_some());
    let require_gpu_failed = settings.require_gpu && !saw_gpu;
    Ok((
        QualificationReport {
            report: "fhegg-bfv-wgpu-qualification-v1",
            host: host_label(),
            adapter,
            gpu_arena_ready,
            settings,
            samples,
            crossover,
            all_bit_exact,
        },
        require_gpu_failed,
    ))
}

fn main() {
    let (report, require_gpu_failed) = match run() {
        Ok(result) => result,
        Err(error) => {
            eprintln!("gpu_fold_qualify: {error}");
            std::process::exit(2);
        }
    };
    match serde_json::to_string_pretty(&report) {
        Ok(json) => println!("{json}"),
        Err(error) => {
            eprintln!("gpu_fold_qualify: could not serialize report: {error}");
            std::process::exit(2);
        }
    }
    if !report.all_bit_exact {
        eprintln!("gpu_fold_qualify: selected backend diverged from the CPU oracle");
        std::process::exit(1);
    }
    if require_gpu_failed {
        eprintln!("gpu_fold_qualify: GPU was required but no sample dispatched through wgpu");
        std::process::exit(3);
    }
}
