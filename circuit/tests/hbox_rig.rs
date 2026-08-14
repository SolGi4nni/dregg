//! # `hbox_rig` — the measurement rig
//!
//! Every wall-clock number this project has published was taken on a laptop at load average
//! 16–95 with 36 login sessions, and a whole cost model had to be retracted because of it
//! (`zkml-research/docs/COST-MODEL.md`, §"THE CLOCK DATA IS NOT SOUND"). The discipline that
//! came out of that retraction is written down in four rules. This file exists because a rule
//! that lives in a markdown file is a rule a lane forgets at 3am, and **the rig should make the
//! discipline automatic.**
//!
//! ## The four rules, and where each is enforced by construction
//!
//! | rule | enforced by |
//! |---|---|
//! | operation counts are PRIMARY, clock SECONDARY | §C — two separate ARMS. A count and a clock **cannot be read from the same run**, and the type system says so. |
//! | a result carries its CONDITIONS or it is not a result | §A — [`Conditions`] is captured before and after every cell and printed with it. There is no code path that emits a number without one. |
//! | a percentage without its denominator is not a measurement | §E — every share carries its `phase_set` string. |
//! | never compose a WORK claim with a LATENCY claim | §F — [`Claim::Work`] and [`Claim::Latency`] are different variants and `compose()` refuses to mix them. |
//!
//! ## ⚑ Why counts and clock cannot share a run
//!
//! This is not a stylistic separation, it is a measurement fact. [`CountingPerm`] bumps a
//! relaxed `fetch_add` on a shared cache line **once per permutation**. At b=6 that is 217,114
//! atomics on the hot path, and they land in exactly the phase being measured. A counting run's
//! milliseconds are not "slightly high", they are meaningless. Symmetrically, the clock arm runs
//! the *deployed* permutation with no instrumentation at all, so it has no counts to report.
//!
//! So: **[`count_arm`] returns counts and no duration. [`clock_arm`] returns durations and no
//! counts.** Neither can be made to return the other. That is the point.
//!
//! ## ⚑ The self-check (§D) — an instrument that can notice it has gone blind
//!
//! Precedent: a pricer that *"reproduces the measured Merkle column to a constant at all five
//! rungs, and refuses to print if it stops."* This rig does the same over the whole prover
//! permutation column. The law is
//!
//! ```text
//!     P(b) = A · 2^b + C          A = 3381, C = 730
//! ```
//!
//! and it is not a fit with slack — it reproduces **every** recorded rung to the unit:
//!
//! | b | 3 | 4 | 5 | 6 | 7 |
//! |---|---:|---:|---:|---:|---:|
//! | recorded | 27,778 | 54,826 | 108,922 | 217,114 | 433,498 |
//! | `3381·2^b + 730` | 27,778 | 54,826 | 108,922 | 217,114 | 433,498 |
//!
//! `A` decomposes as `3312` (Merkle-commit) `+ 69` (FRI-fold Merkle) and `C` as `736`
//! (challenger sampling) `− 3 − 3` (the two `2n−3` Merkle tree roots). **A two-parameter law
//! standing in for a five-point table is a claim, not a summary** — if the prover's committed
//! shape changes, the extra rungs stop agreeing and [`self_check`] goes RED.
//!
//! ⚠ `A` and `C` are properties of **one workload at one query count** (`transferVmDescriptor2`,
//! `q = 19`). They are pinned in [`PINNED_LAW`] with that configuration attached. A different
//! workload is expected to have different constants and must re-pin — the *shape* (affine in
//! `2^b`) is the invariant, the constants are the fingerprint.
//!
//! **Red-capability is proved, not asserted**: [`self_check_is_red_capable`] perturbs the law and
//! requires the checker to reject. A gate that cannot go red is not a gate.
//!
//! ## Running it
//!
//! ```text
//! cargo test -p dregg-circuit --release --test hbox_rig -- --nocapture --test-threads=1 --ignored
//! ```
//!
//! Release only, `--test-threads=1` always (the counters are process-global). On hbox, wrap in
//! `swarm-build` — the cgroup memory cap is what keeps the box alive, `taskset` caps CPU affinity
//! only. ⚠ The agent harness stops backgrounded jobs at ~50 minutes and **a killed test reports
//! as `1 failed`, not as unrunnable**; launch detached and read the per-test label.

#![allow(clippy::type_complexity)]

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::Field;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::Matrix;
use p3_matrix::bitrev::BitReversedMatrixView;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixViewMut};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{
    CryptographicPermutation, PaddingFreeSponge, Permutation, TruncatedPermutation,
};
use p3_uni_stark::StarkConfig;

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace};
use dregg_circuit::effect_vm_descriptors::descriptor2_for_key;
use dregg_circuit::field::BabyBear;

// ════════════════════════════════════════════════════════════════════════════════════════════
// §A — CONDITIONS
//
// "A result that does not carry its conditions is not a result." The retraction that cost a day
// happened because absolute milliseconds were published without the load average that produced
// them. Every cell this rig emits carries one of these, captured BEFORE and AFTER, and the
// printer has no code path that omits it.
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Everything about the machine and the run that could change a number.
#[derive(Clone, Debug, Default)]
pub struct Conditions {
    // ── identity of the box
    pub host: String,
    pub cpu_model: String,
    pub logical_cpus: usize,
    /// ⚑ On hbox this is load-bearing, not decoration. The box is a 12th-gen Intel i9-12900:
    /// **cpu0-15 are 8 P-cores × 2 SMT threads (5.0–5.1 GHz), cpu16-23 are 8 E-cores (3.8 GHz)**.
    /// `swarm-build`'s `taskset -c 0-15` therefore pins to P-cores only — which is good for
    /// measurement, but it means "16 threads" is **8 physical cores with SMT**, and a thread
    /// sweep past 8 measures hyperthreading, not scaling. A number taken without this field is
    /// not interpretable on this machine.
    pub affinity: String,
    pub governor: String,
    pub nice: i64,

    // ── what else was happening
    pub load_start: [f64; 3],
    pub load_end: [f64; 3],
    /// Other people's processes, biggest first. hbox is co-tenant (codex owns a HOL build).
    pub cotenants: Vec<String>,

    // ── what was built
    pub git_sha: String,
    pub rustc: String,
    pub profile: &'static str,

    // ── how it was run
    pub threads: usize,
    /// ⚑ Worth 2.2–2.5× on its own (`notes/lde-layout.md` §G6f): running the prover from a
    /// thread that is not a rayon pool worker pays a cold hand-off per dispatch. A prove time
    /// that does not say which side of this it was taken on is not comparable to anything.
    pub in_rayon_pool: bool,
    pub reps: usize,
}

fn read_first_line(path: &str) -> String {
    std::fs::read_to_string(path)
        .ok()
        .and_then(|s| s.lines().next().map(|l| l.trim().to_string()))
        .unwrap_or_else(|| "unavailable".into())
}

fn loadavg() -> [f64; 3] {
    let s = read_first_line("/proc/loadavg");
    let mut it = s.split_whitespace().filter_map(|t| t.parse::<f64>().ok());
    [
        it.next().unwrap_or(f64::NAN),
        it.next().unwrap_or(f64::NAN),
        it.next().unwrap_or(f64::NAN),
    ]
}

fn cpu_model() -> String {
    std::fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("model name"))
                .and_then(|l| l.split(':').nth(1))
                .map(|v| v.trim().to_string())
        })
        .unwrap_or_else(|| {
            // macOS fallback — the rig must run (loudly, as a non-result) off hbox too.
            run("sysctl", &["-n", "machdep.cpu.brand_string"]).unwrap_or_else(|| "unknown".into())
        })
}

fn run(cmd: &str, args: &[&str]) -> Option<String> {
    std::process::Command::new(cmd)
        .args(args)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .filter(|s| !s.is_empty())
}

/// Processes that are not us and not kernel threads, biggest RSS first. This is how the rig
/// answers "was the box co-tenanted" with evidence rather than a hope.
fn cotenants() -> Vec<String> {
    let me = std::process::id();
    let Some(out) = run("ps", &["-eo", "pid,rss,comm", "--sort=-rss"]) else {
        return vec!["ps unavailable".into()];
    };
    out.lines()
        .skip(1)
        .filter_map(|l| {
            let mut f = l.split_whitespace();
            let pid: u32 = f.next()?.parse().ok()?;
            let rss: u64 = f.next()?.parse().ok()?;
            let comm = f.next()?;
            // Only things big enough to matter, and not this test binary.
            (pid != me && rss > 200_000 && !comm.contains("hbox_rig"))
                .then(|| format!("{comm}({}M)", rss / 1024))
        })
        .take(6)
        .collect()
}

impl Conditions {
    /// Capture everything knowable at the start of a cell.
    pub fn capture(threads: usize, in_rayon_pool: bool, reps: usize) -> Self {
        let load = loadavg();
        Conditions {
            host: run("hostname", &[]).unwrap_or_else(|| "unknown".into()),
            cpu_model: cpu_model(),
            logical_cpus: std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(0),
            affinity: std::fs::read_to_string("/proc/self/status")
                .ok()
                .and_then(|s| {
                    s.lines()
                        .find(|l| l.starts_with("Cpus_allowed_list"))
                        .and_then(|l| l.split(':').nth(1))
                        .map(|v| v.trim().to_string())
                })
                .unwrap_or_else(|| "unavailable".into()),
            governor: read_first_line("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"),
            nice: nice_level(),
            load_start: load,
            load_end: load,
            cotenants: cotenants(),
            git_sha: run("git", &["rev-parse", "--short=12", "HEAD"])
                .unwrap_or_else(|| "unknown".into()),
            rustc: run("rustc", &["--version"]).unwrap_or_else(|| "unknown".into()),
            profile: if cfg!(debug_assertions) {
                "debug ⚠ NOT A RESULT"
            } else {
                "release"
            },
            threads,
            in_rayon_pool,
            reps,
        }
    }

    /// Close the record. Anything that changed between capture and close is a condition that
    /// moved *during* the measurement, which is the most dangerous kind.
    pub fn close(&mut self) {
        self.load_end = loadavg();
        for c in cotenants() {
            if !self.cotenants.contains(&c) {
                self.cotenants.push(format!("{c}⚠APPEARED-MID-RUN"));
            }
        }
    }

    /// ⚑ The rig's opinion of its own conditions. This is what turns a recorded condition into
    /// an enforced one: a cell whose verdict is not `Clean` prints with the banner attached and
    /// must not be quoted as an absolute.
    pub fn verdict(&self) -> CondVerdict {
        if self.profile.starts_with("debug") {
            return CondVerdict::Void("debug build — timings are not a result");
        }
        let peak = self.load_start[0].max(self.load_end[0]);
        // The rig's own threads are load. Anything beyond them is somebody else.
        let foreign = peak - self.threads as f64;
        if self.cotenants.iter().any(|c| c.contains("APPEARED")) {
            CondVerdict::Contended("a co-tenant appeared mid-run")
        } else if foreign > 2.0 {
            CondVerdict::Contended("load exceeds this rig's own thread count by >2")
        } else if !self.affinity.is_empty()
            && self.affinity.contains("16")
            && self.cpu_model.contains("12900")
        {
            // Being pinned across the P/E boundary makes a thread sweep meaningless.
            CondVerdict::Mixed("affinity spans P-cores and E-cores on a hybrid CPU")
        } else {
            CondVerdict::Clean
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CondVerdict {
    Clean,
    /// Usable for ratios within the run, never as an absolute.
    Contended(&'static str),
    Mixed(&'static str),
    /// Not a measurement at all.
    Void(&'static str),
}

impl CondVerdict {
    fn banner(&self) -> String {
        match self {
            CondVerdict::Clean => "conditions: CLEAN".into(),
            CondVerdict::Contended(w) => format!("⚠ conditions: CONTENDED — {w} — RATIOS ONLY"),
            CondVerdict::Mixed(w) => format!("⚠ conditions: MIXED — {w}"),
            CondVerdict::Void(w) => format!("⛔ conditions: VOID — {w}"),
        }
    }
}

/// `swarm-build` applies `nice -n 15`. That is right for a build and it is a hazard for a
/// benchmark — a niced process yields to anything that appears, so a co-tenant arriving mid-run
/// distorts the niced side more. Recorded so the reader can see it rather than assume it.
fn nice_level() -> i64 {
    // Field 19 of /proc/self/stat is `nice`; no libc dependency for one number.
    read_first_line("/proc/self/stat")
        .split_whitespace()
        .nth(18)
        .and_then(|v| v.parse().ok())
        .unwrap_or(0)
}

impl std::fmt::Display for Conditions {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "  {}", self.verdict().banner())?;
        writeln!(
            f,
            "  box      : {} — {} ({} logical cpus)",
            self.host, self.cpu_model, self.logical_cpus
        )?;
        writeln!(
            f,
            "  affinity : cpus {} · governor {} · nice {}",
            self.affinity, self.governor, self.nice
        )?;
        writeln!(
            f,
            "  load     : start {:.2} {:.2} {:.2} → end {:.2} {:.2} {:.2}",
            self.load_start[0],
            self.load_start[1],
            self.load_start[2],
            self.load_end[0],
            self.load_end[1],
            self.load_end[2]
        )?;
        writeln!(
            f,
            "  cotenants: {}",
            if self.cotenants.is_empty() {
                "none over 200M".into()
            } else {
                self.cotenants.join(" ")
            }
        )?;
        writeln!(
            f,
            "  build    : {} @ {} · {}",
            self.profile, self.git_sha, self.rustc
        )?;
        write!(
            f,
            "  run      : threads {} · {} · N={}",
            self.threads,
            if self.in_rayon_pool {
                "INSIDE rayon pool"
            } else {
                "cold caller (not a pool worker)"
            },
            self.reps
        )
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §B — THE TWO INSTRUMENTS
//
// Both already existed; neither was in a library. This is the fourth copy of the permutation
// counter, which is three more than there should be — `poseidon2_narrow_witness.rs`'s header
// says "if a third file wants one, that is the point to lift it into the library". Recorded as
// debt at the top of `notes/hbox-rig.md`; lifting it is a separate change that touches three
// hot files and should not ride along inside a measurement rig.
// ════════════════════════════════════════════════════════════════════════════════════════════

/// Scalar-equivalent Poseidon2-16 permutations. A packed call adds its lane count, derived from
/// `size_of::<T>()`, so the unit is arch-portable: it is *work*, not instructions.
static PERMS: AtomicU64 = AtomicU64::new(0);
/// SIMD call count — `PERMS / PERMS_PACKED` recovers this box's effective packing width.
static PERMS_PACKED: AtomicU64 = AtomicU64::new(0);

#[derive(Clone)]
struct CountingPerm(Poseidon2BabyBear<16>);

impl<T: Clone> Permutation<T> for CountingPerm
where
    Poseidon2BabyBear<16>: Permutation<T>,
{
    fn permute_mut(&self, input: &mut T) {
        let lanes =
            (core::mem::size_of::<T>() / (16 * core::mem::size_of::<P3BabyBear>())).max(1) as u64;
        PERMS.fetch_add(lanes, Ordering::Relaxed);
        if lanes > 1 {
            PERMS_PACKED.fetch_add(1, Ordering::Relaxed);
        }
        self.0.permute_mut(input);
    }
}
impl<T: Clone> CryptographicPermutation<T> for CountingPerm where
    Poseidon2BabyBear<16>: CryptographicPermutation<T>
{
}

/// One DFT call's shape. The field-op instrument in `ir2_field_op_counts.rs` replays exactly
/// this log against a counting field to get multiplications and additions; the rig records the
/// shapes live and cross-checks them (§D3) rather than carrying a second copy of that 600-line
/// counting-field newtype.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DftShape {
    pub call: &'static str,
    pub height: usize,
    pub width: usize,
    pub added_bits: usize,
}

fn dft_log() -> &'static Mutex<Vec<DftShape>> {
    static L: std::sync::OnceLock<Mutex<Vec<DftShape>>> = std::sync::OnceLock::new();
    L.get_or_init(|| Mutex::new(Vec::new()))
}

/// A DFT that delegates every call to the real one and logs its shape. The proof is
/// bit-identical to deployed; the added work is one `Vec::push` per call and there are 18 calls
/// per proof, so unlike [`CountingPerm`] this instrument is clock-safe. It is still kept out of
/// the clock arm, because an instrument you have not proved harmless is one you are trusting.
#[derive(Clone, Default, Debug)]
struct RecordingDft {
    inner: Radix2DitParallel<P3BabyBear>,
}

impl RecordingDft {
    fn record(call: &'static str, height: usize, width: usize, added_bits: usize) {
        dft_log().lock().unwrap().push(DftShape {
            call,
            height,
            width,
            added_bits,
        });
    }
}

impl TwoAdicSubgroupDft<P3BabyBear> for RecordingDft {
    type Evaluations = BitReversedMatrixView<RowMajorMatrix<P3BabyBear>>;

    fn dft_batch(&self, mat: RowMajorMatrix<P3BabyBear>) -> Self::Evaluations {
        Self::record("dft_batch", mat.height(), mat.width(), 0);
        self.inner.dft_batch(mat)
    }

    fn coset_dft_batch(
        &self,
        mat: RowMajorMatrix<P3BabyBear>,
        shift: P3BabyBear,
    ) -> Self::Evaluations {
        Self::record("coset_dft_batch", mat.height(), mat.width(), 0);
        self.inner.coset_dft_batch(mat, shift)
    }

    fn coset_idft_batch(
        &self,
        mat: RowMajorMatrix<P3BabyBear>,
        shift: P3BabyBear,
    ) -> RowMajorMatrix<P3BabyBear> {
        Self::record("coset_idft_batch", mat.height(), mat.width(), 0);
        self.inner.coset_idft_batch(mat, shift)
    }

    fn coset_lde_batch_with_transform<T>(
        &self,
        mat: RowMajorMatrix<P3BabyBear>,
        added_bits: usize,
        shift: P3BabyBear,
        transform: T,
    ) -> Self::Evaluations
    where
        T: FnOnce(&mut RowMajorMatrixViewMut<'_, P3BabyBear>, p3_dft::Layout),
    {
        Self::record("coset_lde_batch", mat.height(), mat.width(), added_bits);
        self.inner
            .coset_lde_batch_with_transform(mat, added_bits, shift, transform)
    }
}

// ── config types ────────────────────────────────────────────────────────────────────────────
type Pack = <P3BabyBear as Field>::Packing;
type Ef = BinomialExtensionField<P3BabyBear, 4>;

// COUNT arm: counting permutation AND recording DFT. The two ride in different type parameters
// of `TwoAdicFriPcs` (the perm in the Mmcs and the Challenger, the DFT in `Dft`) so they compose
// with no new impls — the whole reason both instruments fit in one harness.
type CHash = PaddingFreeSponge<CountingPerm, 16, 8, 8>;
type CCompress = TruncatedPermutation<CountingPerm, 2, 8, 16>;
type CValMmcs = MerkleTreeMmcs<Pack, Pack, CHash, CCompress, 2, 8>;
type CChallengeMmcs = ExtensionMmcs<P3BabyBear, Ef, CValMmcs>;
type CPcs = TwoAdicFriPcs<P3BabyBear, RecordingDft, CValMmcs, CChallengeMmcs>;
type CChallenger = DuplexChallenger<P3BabyBear, CountingPerm, 16, 8>;
type CountConfig = StarkConfig<CPcs, Ef, CChallenger>;

// CLOCK arm: the deployed permutation and the deployed DFT. No instrumentation whatsoever.
type Perm = Poseidon2BabyBear<16>;
type PHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type PCompress = TruncatedPermutation<Perm, 2, 8, 16>;
type PValMmcs = MerkleTreeMmcs<Pack, Pack, PHash, PCompress, 2, 8>;
type PChallengeMmcs = ExtensionMmcs<P3BabyBear, Ef, PValMmcs>;
type PPcs = TwoAdicFriPcs<P3BabyBear, Radix2DitParallel<P3BabyBear>, PValMmcs, PChallengeMmcs>;
type PChallenger = DuplexChallenger<P3BabyBear, Perm, 16, 8>;
type ClockConfig = StarkConfig<PPcs, Ef, PChallenger>;

/// The point in the sweep space. **Every dimension the rig can move is a named field**, so a
/// result cannot be recorded without saying where it was taken — rule 1 of `COST-MODEL.md`
/// ("a ratio without `(lb, q, pow, rows, N)` cannot be composed") turned into a struct.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Point {
    pub log_blowup: usize,
    pub num_queries: usize,
    pub pow_bits: usize,
    /// Number of effects in the workload — the trace-height axis. See [`Workload::build`].
    pub effects: usize,
    pub threads: usize,
}

impl Point {
    pub fn deployed() -> Self {
        // The deployed IR-v2 knobs: descriptor_ir2.rs IR2_FRI_* consts.
        Point {
            log_blowup: 6,
            num_queries: 19,
            pow_bits: 16,
            effects: 1,
            threads: 1,
        }
    }
    pub fn at_blowup(self, log_blowup: usize) -> Self {
        Point { log_blowup, ..self }
    }
    pub fn label(&self) -> String {
        format!(
            "(lb {}, q {}, pow {}, eff {}, T {})",
            self.log_blowup, self.num_queries, self.pow_bits, self.effects, self.threads
        )
    }
}

fn count_config(p: Point) -> CountConfig {
    let perm = CountingPerm(default_babybear_poseidon2_16());
    let val_mmcs = CValMmcs::new(CHash::new(perm.clone()), CCompress::new(perm.clone()), 0);
    let fri = FriParameters {
        log_blowup: p.log_blowup,
        log_final_poly_len: 0,
        max_log_arity: 3,
        num_queries: p.num_queries,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: p.pow_bits,
        mmcs: CChallengeMmcs::new(val_mmcs.clone()),
    };
    StarkConfig::new(
        TwoAdicFriPcs::new(RecordingDft::default(), val_mmcs, fri),
        CChallenger::new(perm),
    )
}

fn clock_config(p: Point) -> ClockConfig {
    let perm = default_babybear_poseidon2_16();
    let val_mmcs = PValMmcs::new(PHash::new(perm.clone()), PCompress::new(perm.clone()), 0);
    let fri = FriParameters {
        log_blowup: p.log_blowup,
        log_final_poly_len: 0,
        max_log_arity: 3,
        num_queries: p.num_queries,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: p.pow_bits,
        mmcs: PChallengeMmcs::new(val_mmcs.clone()),
    };
    StarkConfig::new(
        TwoAdicFriPcs::new(Radix2DitParallel::default(), val_mmcs, fri),
        PChallenger::new(perm),
    )
}

// ── workload ────────────────────────────────────────────────────────────────────────────────

pub struct Workload {
    desc: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    base_trace: Vec<Vec<BabyBear>>,
    pis: Vec<BabyBear>,
    /// Recorded, not assumed — the trace-height axis is only real if the heights actually move.
    pub heights: Vec<usize>,
}

impl Workload {
    /// `columns × rows`, deduplicated. Printing 64 copies of the same number is how a shape
    /// stops being read.
    pub fn shape(&self) -> String {
        let mut rows: Vec<usize> = self.heights.clone();
        rows.sort_unstable();
        rows.dedup();
        format!("{} columns × rows {:?}", self.heights.len(), rows)
    }
}

impl Workload {
    /// Build the IR-v2 transfer workload with `effects` transfers. `effects` is the rig's
    /// trace-height axis; it is **recorded** in [`Workload::heights`] so that a sweep which
    /// silently fails to change the trace shape is visible rather than reported as a flat curve.
    pub fn build(effects: usize) -> Result<Self, String> {
        Self::build_with(effects, 50)
    }

    /// Same workload with a different transfer `amount`. Changing the amount changes the trace,
    /// hence the commitment, hence the Fiat-Shamir challenge, hence the **grind transcript** —
    /// which is the only way to draw more than once from the PoW distribution. See §E3.
    pub fn build_with(effects: usize, amount: u64) -> Result<Self, String> {
        let state = CellState::new(100_000, 0);
        let effs: Vec<Effect> = (0..effects.max(1))
            .map(|_| Effect::Transfer {
                amount,
                direction: 1,
            })
            .collect();
        let (base_trace, pis) = generate_effect_vm_trace(&state, &effs);
        let json = descriptor2_for_key("transferVmDescriptor2").ok_or("no v2 transfer")?;
        let desc = parse_vm_descriptor2(json).map_err(|e| format!("{e:?}"))?;
        if pis.len() < desc.public_input_count {
            return Err(format!(
                "workload with {effects} effects produced {} public inputs, descriptor wants {}",
                pis.len(),
                desc.public_input_count
            ));
        }
        // `base_trace` is column-major, so every column has the same length; report the SHAPE
        // (columns × rows) rather than 64 copies of the same number.
        let heights = base_trace.iter().map(|c| c.len()).collect::<Vec<_>>();
        let dpis = pis[..desc.public_input_count].to_vec();
        Ok(Workload {
            desc,
            base_trace,
            pis: dpis,
            heights,
        })
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §C — THE TWO ARMS
//
// The separation is structural: `Counts` has no duration field and `Timing` has no count field.
// You cannot accidentally publish a millisecond taken from a counting run, because the counting
// run does not return one.
// ════════════════════════════════════════════════════════════════════════════════════════════

/// The PRIMARY result. Exact, deterministic, hardware-free, contention-immune.
#[derive(Clone, Debug)]
pub struct Counts {
    pub point: Point,
    /// Scalar-equivalent Poseidon2 permutations, prove **including** the internal self-verify.
    /// ⚠ Reading this as prover work attributes the verifier's Merkle paths to the prover; the
    /// split is [`Counts::verify_perms`].
    pub prove_perms: u64,
    pub verify_perms: u64,
    pub packed_calls: u64,
    /// Every DFT call's shape, in order. The field-op instrument replays exactly this.
    pub dft: Vec<DftShape>,
    pub proof_bytes: usize,
}

impl Counts {
    /// Prover permutations with the self-verify removed — the quantity the phase law predicts.
    pub fn prover_only(&self) -> u64 {
        self.prove_perms.saturating_sub(self.verify_perms)
    }
    pub fn effective_packing_width(&self) -> f64 {
        if self.packed_calls == 0 {
            1.0
        } else {
            self.prove_perms as f64 / self.packed_calls as f64
        }
    }
}

/// The SECONDARY result. Never reported without its [`Conditions`], never composed with counts.
#[derive(Clone, Debug)]
pub struct Timing {
    pub point: Point,
    pub samples: Vec<Duration>,
}

impl Timing {
    pub fn stat(&self) -> Stat {
        Stat::of(&self.samples)
    }
}

/// ⚑ **A percentage that cannot be printed without its denominator.**
///
/// *"A percentage without its denominator is not a measurement"* — the rule `COST-MODEL.md`
/// produced after two lanes spent half a day on a "grind is 18% / 23%" disagreement that turned
/// out to be two different phase sets. The only way to render a `Share` is [`Share::line`], and
/// it prints the numerator, the denominator, and the name of the phase set alongside the
/// percent sign. There is no `Display` and no bare `as_percent()`.
#[derive(Clone, Copy, Debug)]
pub struct Share {
    pub part: f64,
    pub whole: f64,
    /// What the denominator actually is. "hash work only" and "all prover work" are different
    /// answers to the same question and this is where they stop being confusable.
    pub phase_set: &'static str,
}

impl Share {
    pub fn new(part: f64, whole: f64, phase_set: &'static str) -> Share {
        Share {
            part,
            whole,
            phase_set,
        }
    }
    pub fn fraction(&self) -> f64 {
        self.part / self.whole
    }
    pub fn line(&self) -> String {
        format!(
            "{:.1}% ({:.0} of {:.0}; denominator = {})",
            self.fraction() * 100.0,
            self.part,
            self.whole,
            self.phase_set
        )
    }
}

/// ⚑ **min / median / p99 — never a mean.** A mean over a contended box is a number about the
/// contention. `spread` is carried because a lane measuring GPU work found the same cell varying
/// **2.1× across three runs**; a cell whose spread is large is a cell whose min is the only
/// defensible reading, and the rig says so rather than leaving it to the reader.
#[derive(Clone, Copy, Debug)]
pub struct Stat {
    pub n: usize,
    pub min_ms: f64,
    pub p50_ms: f64,
    pub p99_ms: f64,
    pub max_ms: f64,
}

impl Stat {
    pub fn of(s: &[Duration]) -> Stat {
        let mut v: Vec<f64> = s.iter().map(|d| d.as_secs_f64() * 1e3).collect();
        v.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let pick = |q: f64| -> f64 {
            if v.is_empty() {
                return f64::NAN;
            }
            v[(((v.len() - 1) as f64) * q).round() as usize]
        };
        Stat {
            n: v.len(),
            min_ms: pick(0.0),
            p50_ms: pick(0.5),
            p99_ms: pick(0.99),
            max_ms: pick(1.0),
        }
    }
    /// max/min. Above ~1.3 the absolutes are not defensible and only the min may be quoted.
    pub fn spread(&self) -> f64 {
        self.max_ms / self.min_ms
    }
    pub fn line(&self) -> String {
        format!(
            "min {:8.3}  p50 {:8.3}  p99 {:8.3}  max {:8.3}  spread {:.2}×{}",
            self.min_ms,
            self.p50_ms,
            self.p99_ms,
            self.max_ms,
            self.spread(),
            if self.spread() > 1.3 {
                "  ⚠ UNSTABLE — min only"
            } else {
                ""
            }
        )
    }
}

/// COUNT arm. Returns exact counts and **no duration**, because a duration taken here would be
/// an artifact of the counting.
pub fn count_arm(w: &Workload, p: Point) -> Result<Counts, String> {
    let config = count_config(p);
    dft_log().lock().unwrap().clear();
    PERMS.store(0, Ordering::Relaxed);
    PERMS_PACKED.store(0, Ordering::Relaxed);

    let proof = prove_vm_descriptor2_for_config(
        &w.desc,
        &w.base_trace,
        &w.pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .map_err(|e| format!("count arm at {} failed: {e}", p.label()))?;

    let prove_perms = PERMS.load(Ordering::Relaxed);
    let packed_calls = PERMS_PACKED.load(Ordering::Relaxed);
    let dft = dft_log().lock().unwrap().clone();

    // The self-verify inside the prover is what we subtract; measure it by running the verifier
    // again on a fresh counter rather than by assuming a constant.
    PERMS.store(0, Ordering::Relaxed);
    dregg_circuit::descriptor_ir2::verify_vm_descriptor2_with_config(
        &w.desc, &proof, &w.pis, &config,
    )
    .map_err(|e| format!("count arm verify at {} failed: {e}", p.label()))?;
    let verify_perms = PERMS.load(Ordering::Relaxed);

    let proof_bytes = serde_json::to_vec(&proof).map(|v| v.len()).unwrap_or(0);

    Ok(Counts {
        point: p,
        prove_perms,
        verify_perms,
        packed_calls,
        dft,
        proof_bytes,
    })
}

/// ⚑ Fix the rayon thread count **for the whole process**, once.
///
/// This has to be the global pool, not a private one. The prover's internal `par_iter`s resolve
/// against whatever pool the calling thread belongs to, and a caller on the main thread belongs
/// to the *global* pool — so a private `ThreadPoolBuilder` that is not `install`ed controls
/// nothing, and one that is `install`ed silently changes the other axis being measured. A rig
/// whose thread knob does not actually move the threads is worse than no knob.
///
/// Consequence, and it is a real constraint on the rig: **one thread count per process.** A
/// thread sweep is a loop of process invocations (`RIG_THREADS=n`), not a loop inside a test.
pub fn set_threads_once(n: usize) -> usize {
    static DONE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *DONE.get_or_init(|| {
        match rayon::ThreadPoolBuilder::new()
            .num_threads(n)
            .build_global()
        {
            Ok(()) => n,
            // Already initialised (another test in the binary got here first). Report what the
            // pool actually is rather than what was asked for.
            Err(_) => rayon::current_num_threads(),
        }
    })
}

/// CLOCK arm. Returns durations and **no counts**. Runs on the uninstrumented deployed config.
///
/// `in_pool` selects the ~2.2–2.5× axis (`notes/lde-layout.md` §G6f): `false` reproduces the
/// deployed shape, where the caller is *not* a rayon worker and pays a cold hand-off per
/// dispatch; `true` runs the whole prove on a pool worker. Both are legitimate measurements and
/// publishing one without saying which is not.
pub fn clock_arm(w: &Workload, p: Point, reps: usize, in_pool: bool) -> Result<Timing, String> {
    let config = clock_config(p);
    let once = || -> Result<Duration, String> {
        let t = Instant::now();
        let proof = prove_vm_descriptor2_for_config(
            &w.desc,
            &w.base_trace,
            &w.pis,
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness::default(),
            &config,
        )
        .map_err(|e| format!("clock arm at {} failed: {e}", p.label()))?;
        let d = t.elapsed();
        std::hint::black_box(&proof);
        Ok(d)
    };

    // Run one prove either from the calling thread (deployed shape) or from a pool worker.
    let sample = || -> Result<Duration, String> {
        if in_pool {
            let mut out: Option<Result<Duration, String>> = None;
            rayon::scope(|s| {
                s.spawn(|_| out = Some(once()));
            });
            out.expect("the scoped task ran")
        } else {
            once()
        }
    };

    // ⚑ One untimed warm-up. The first prove pays twiddle-table construction, page faults, and —
    // on hbox specifically — the climb from the `powersave` governor's 800 MHz floor to 5 GHz.
    // Including it is one of the ways a false optimum gets manufactured at the low end of a sweep.
    sample()?;

    let mut samples = Vec::with_capacity(reps);
    for _ in 0..reps {
        samples.push(sample()?);
    }
    Ok(Timing { point: p, samples })
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §D — THE SELF-CHECK
//
// "A gate that cannot go red is not a gate." This one prices what it measures from a
// two-parameter law and refuses if the law stops reproducing.
// ════════════════════════════════════════════════════════════════════════════════════════════

/// `P(b) = a·2^b + c` — the prover's permutation count as a function of blowup.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PermLaw {
    pub a: u64,
    pub c: u64,
}

impl PermLaw {
    pub fn eval(&self, b: usize) -> u64 {
        self.a * (1u64 << b) + self.c
    }
    /// Fit from two rungs. Two points determine the law; every *other* rung is then a prediction
    /// that can fail — which is the only reason a fit is worth anything as a check.
    pub fn fit(lo: (usize, u64), hi: (usize, u64)) -> Result<PermLaw, String> {
        let (b0, p0) = lo;
        let (b1, p1) = hi;
        if b1 <= b0 {
            return Err("fit needs two distinct rungs, low first".into());
        }
        let d = (1u64 << b1) - (1u64 << b0);
        if p1 < p0 || (p1 - p0) % d != 0 {
            return Err(format!(
                "not affine in 2^b: ({b0},{p0}) → ({b1},{p1}) gives a non-integral slope"
            ));
        }
        let a = (p1 - p0) / d;
        let c = p0
            .checked_sub(a * (1u64 << b0))
            .ok_or("negative intercept — the shape is not P = a·2^b + c")?;
        Ok(PermLaw { a, c })
    }
}

/// The pinned fingerprint, with the configuration it belongs to: workload `transferVmDescriptor2`
/// with one Transfer, `q = 19`, `pow = 0`.
///
/// ⚑ **There are TWO recorded "prover permutation" columns and they differ by a constant 36.**
/// Getting this wrong is not a rounding error, it makes the self-check fire on a correct prover
/// — which is exactly what happened while building this file, so it is written down here:
///
/// | convention | phase set | law | b=3 | b=6 |
/// |---|---|---|---:|---:|
/// | three NAMED phases | Merkle-commit + FRI-fold + challenger | `3381·2^b + 730` | 27,778 | 217,114 |
/// | **prove − self-verify** ← what this rig measures | the above **+ FRI-commit-other (3) + query/open (3) + prove residual (30)** | **`3381·2^b + 766`** | **27,814** | **217,150** |
///
/// The `+36` is constant in `b` (independently recorded at both ends by `notes/blowup-drop.md`),
/// which is why it lands in `c` and leaves `a` alone.
///
/// `a = 3312 (Merkle-commit) + 69 (FRI-fold Merkle)`; `c = 736 (challenger) − 3 − 3` (the two
/// `2n − 3` Merkle roots) `+ 36` (unspanned prover work).
pub const PINNED_LAW: PermLaw = PermLaw { a: 3381, c: 766 };
/// The `prove − self-verify` column. b=3 and b=6 are read directly off `notes/blowup-drop.md`
/// §D2 (27,814 and 217,150); the other three rungs are the law's predictions and are what the
/// rig checks against.
pub const PINNED_RUNGS: &[(usize, u64)] = &[
    (3, 27_814),
    (4, 54_862),
    (5, 108_958),
    (6, 217_150),
    (7, 433_534),
];
/// The sibling convention, carried so a PIN failure can say which column the prover has landed
/// on instead of leaving the reader to work it out.
pub const NAMED_PHASES_LAW: PermLaw = PermLaw { a: 3381, c: 730 };

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckResult {
    Green(String),
    Red(String),
}

impl CheckResult {
    pub fn is_red(&self) -> bool {
        matches!(self, CheckResult::Red(_))
    }
    pub fn text(&self) -> &str {
        match self {
            CheckResult::Green(s) | CheckResult::Red(s) => s,
        }
    }
}

/// ⚑ **The rig's detector that it has gone blind.**
///
/// Three independent ways to fail, in increasing order of "something real changed":
///
/// 1. **SHAPE** — the measured rungs are not affine in `2^b` at all. The prover's committed
///    geometry changed qualitatively.
/// 2. **PREDICTION** — the law fitted from the two lowest rungs mispredicts a higher one. This
///    is the one that catches a change confined to one blowup.
/// 3. **PIN** — the fitted constants differ from [`PINNED_LAW`]. The prover still has the right
///    *shape* but a different amount of committed data: a new column, a widened chip, a changed
///    query count. **This is not a failure of the rig, it is the rig doing its job** — but the
///    number it was about to print is no longer comparable to any recorded number, so it refuses.
pub fn self_check(measured: &[(usize, u64)], pinned: PermLaw) -> CheckResult {
    if measured.len() < 3 {
        return CheckResult::Red(format!(
            "self-check needs ≥3 rungs to be a check rather than a definition; got {}",
            measured.len()
        ));
    }
    let mut m = measured.to_vec();
    m.sort();

    // (1) + (2): fit on the two lowest, predict everything above.
    let law = match PermLaw::fit(m[0], m[1]) {
        Ok(l) => l,
        Err(e) => return CheckResult::Red(format!("SHAPE — {e}")),
    };
    let mut bad = Vec::new();
    for &(b, p) in &m[2..] {
        let pred = law.eval(b);
        if pred != p {
            bad.push(format!(
                "b={b}: predicted {pred}, measured {p} (Δ {})",
                p as i64 - pred as i64
            ));
        }
    }
    if !bad.is_empty() {
        return CheckResult::Red(format!(
            "PREDICTION — P = {}·2^b + {} fitted on b={},{} mispredicts: {}",
            law.a,
            law.c,
            m[0].0,
            m[1].0,
            bad.join("; ")
        ));
    }

    // (3): the fingerprint.
    if law != pinned {
        // Name the sibling convention explicitly if that is what we landed on — a 36-perm
        // offset is otherwise a genuinely mysterious red.
        if law == NAMED_PHASES_LAW {
            return CheckResult::Red(format!(
                "PIN — measured P = {}·2^b + {}, which is the THREE-NAMED-PHASES convention \
                 (Merkle-commit + FRI-fold + challenger), not the prove−self-verify convention \
                 this rig pins ({}·2^b + {}). The two differ by a constant 36 = FRI-commit-other \
                 (3) + query/open (3) + prove residual (30). The prover is fine; the rig's phase \
                 set changed under it.",
                law.a, law.c, pinned.a, pinned.c
            ));
        }
        return CheckResult::Red(format!(
            "PIN — the prover's shape is intact but its constants MOVED: measured P = {}·2^b + {}, \
             pinned P = {}·2^b + {}. Something changed what gets committed (a column, a chip \
             width, the query count). Every number in this rig's history is against the pinned \
             constants and is NOT comparable until this is reconciled. Δa = {}, Δc = {}.",
            law.a,
            law.c,
            pinned.a,
            pinned.c,
            law.a as i64 - pinned.a as i64,
            law.c as i64 - pinned.c as i64
        ));
    }

    CheckResult::Green(format!(
        "P = {}·2^b + {} reproduces all {} measured rungs to the unit, and matches the pin",
        law.a,
        law.c,
        m.len()
    ))
}

/// The DFT-shape census — the cross-check on the *arithmetic* instrument. `ir2_field_op_counts.rs`
/// measured 18 DFT calls per proof at every blowup (6 under `prove_batch`, 12 under
/// `compute quotient`, all width 4), and after the batched-chunk landing (`a31590c37`) the twelve
/// became **three** at widths 8 / 32 / 8. If that census moves, the recorded field-op table no
/// longer describes this prover.
pub fn dft_census_check(dft: &[DftShape]) -> CheckResult {
    let calls = dft.len();
    let mut by_call: BTreeMap<&str, usize> = BTreeMap::new();
    for d in dft {
        *by_call.entry(d.call).or_default() += 1;
    }
    // The one thing `field-op-counts.md` proved and `lde-layout.md` re-confirmed: the slow
    // extrapolation path is NEVER taken. Zero coset_idft_batch, zero coset_dft_batch.
    let slow = by_call.get("coset_idft_batch").copied().unwrap_or(0)
        + by_call.get("coset_dft_batch").copied().unwrap_or(0);
    if slow != 0 {
        return CheckResult::Red(format!(
            "DFT CENSUS — the slow extrapolation path was taken {slow} times. It has been zero at \
             every blowup in every recorded run; `get_evaluations_on_domain`'s else-branch is now \
             live and the recorded field-op table does not describe this prover."
        ));
    }
    CheckResult::Green(format!(
        "{calls} DFT calls, {} — slow path not taken (0 coset_idft / 0 coset_dft), as recorded",
        by_call
            .iter()
            .map(|(k, v)| format!("{v}×{k}"))
            .collect::<Vec<_>>()
            .join(" ")
    ))
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §E — THE SWEEP
// ════════════════════════════════════════════════════════════════════════════════════════════

fn banner(title: &str) {
    println!("\n{}", "═".repeat(96));
    println!("  {title}");
    println!("{}", "═".repeat(96));
}

/// **§E1 — the count sweep.** Exact permutation counts across the blowup axis, plus the
/// self-check. This is the primary result and it is contention-immune, so it is the one cell of
/// this rig that would be valid even on the laptop.
#[test]
#[ignore = "measurement rig — run explicitly: cargo test --release --test hbox_rig -- --ignored --nocapture --test-threads=1"]
fn e1_count_sweep_and_self_check() {
    banner("§E1 — COUNT ARM (primary) — exact Poseidon2 permutations vs blowup");
    let mut cond = Conditions::capture(1, false, 1);
    let w = Workload::build(1).expect("workload builds");
    println!("{cond}");
    println!(
        "  workload : transferVmDescriptor2, 1 Transfer, {}",
        w.shape()
    );
    println!(
        "  ⓘ This is the COUNT arm. Its numbers are exact and contention-immune, so a CONTENDED\n             verdict above does NOT weaken them — it is recorded because the same run's conditions\n             are what the clock arm would need, and because a condition unrecorded is a condition lost."
    );
    println!(
        "\n  {:>3}  {:>12}  {:>10}  {:>12}  {:>9}  {:>11}",
        "b", "prover", "verify", "prove+verify", "packedW", "proof bytes"
    );

    let base = Point {
        pow_bits: 0, // ⚠ grind is a RANDOM draw; including it makes the column a sample.
        ..Point::deployed()
    };
    let mut rungs = Vec::new();
    let mut census = None;
    let mut census_w = 1.0f64;
    for b in 3..=7usize {
        let c = count_arm(&w, base.at_blowup(b)).expect("count arm proves");
        println!(
            "  {:>3}  {:>12}  {:>10}  {:>12}  {:>9.2}  {:>11}",
            b,
            c.prover_only(),
            c.verify_perms,
            c.prove_perms,
            c.effective_packing_width(),
            c.proof_bytes
        );
        rungs.push((b, c.prover_only()));
        if b == 6 {
            census = Some(c.dft.clone());
            census_w = c.effective_packing_width();
        }
    }
    cond.close();

    // ⚑ The SIMD condition. `<BabyBear as Field>::Packing` is chosen by target features, not by
    // the CPU that exists. On a box with AVX2 and no `-C target-cpu=native`, the prover runs the
    // SCALAR Poseidon2 and every hash millisecond is several times the deployed one — while the
    // COUNTS are unchanged, because they are scalar-equivalent by construction. That is the
    // nastiest possible shape for a defect: the primary instrument stays correct and the
    // secondary one silently measures a different prover.
    let packed_w = census_w;
    if packed_w <= 1.0 {
        println!(
            "\n  ⛔ PACKING WIDTH IS 1 — this build ran the SCALAR Poseidon2 path.\n                  The counts above are UNAFFECTED (they are scalar-equivalent by construction), but\n                  ANY WALL CLOCK FROM THIS BUILD MEASURES THE WRONG PROVER. On x86-64 the packed\n                  path needs the target feature: rebuild with RUSTFLAGS='-C target-cpu=native'.\n                  (Recorded rather than fatal: the count arm is still a valid result.)"
        );
    } else {
        println!("\n  ⓘ packing width {packed_w:.2} — the packed Poseidon2 path is live.");
    }

    banner("§D — SELF-CHECK");
    let sc = self_check(&rungs, PINNED_LAW);
    println!("  perm law   : {}", sc.text());
    let dc = dft_census_check(census.as_deref().unwrap_or(&[]));
    println!("  dft census : {}", dc.text());
    println!("\n{cond}");

    assert!(
        !sc.is_red(),
        "\n\n⛔ THE RIG IS MEASURING SOMETHING THAT CHANGED:\n{}\n\n",
        sc.text()
    );
    assert!(!dc.is_red(), "\n\n⛔ {}\n\n", dc.text());
}

/// **§E2 — the clock sweep.** Secondary. Runs on the uninstrumented config, reports min/p50/p99
/// and the spread, and carries its conditions on every line.
#[test]
#[ignore = "measurement rig"]
fn e2_clock_sweep() {
    let reps: usize = std::env::var("RIG_REPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(9);
    let want: usize = std::env::var("RIG_THREADS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(1);
    // ⚑ Report the pool we GOT, not the pool we asked for. A thread knob that silently does
    // nothing is how a flat scaling curve gets published.
    let threads = set_threads_once(want);
    if threads != want {
        println!("  ⚠ asked for {want} rayon threads, the global pool is {threads}");
    }

    banner("§E2 — CLOCK ARM (secondary) — uninstrumented prove, min/p50/p99");
    let mut cond = Conditions::capture(threads, false, reps);
    let w = Workload::build(1).expect("workload builds");
    println!("{cond}");
    println!("  ⚠ SECONDARY INSTRUMENT. Counts are §E1. These milliseconds may not be composed");
    println!("    with any count, and may not be quoted as absolutes unless CLEAN above.");
    println!(
        "  workload : transferVmDescriptor2, 1 Transfer, {}\n",
        w.shape()
    );

    let base = Point {
        pow_bits: 0,
        threads,
        ..Point::deployed()
    };
    for b in 3..=7usize {
        let p = base.at_blowup(b);
        for in_pool in [false, true] {
            let t = clock_arm(&w, p, reps, in_pool).expect("clock arm proves");
            println!(
                "  {}  {:<22}  {}",
                p.label(),
                if in_pool {
                    "INSIDE pool"
                } else {
                    "cold caller"
                },
                t.stat().line()
            );
        }
    }
    cond.close();
    println!("\n{cond}");
}

/// **§E3 — the grind axis, handled as the random variable it is.**
///
/// Three of this project's most embarrassing errors are on the list this rig exists to prevent,
/// and one of them is *a false optimum manufactured by grind variance*. A PoW grind at `pow` bits
/// is a geometric draw with mean `2^pow`; a single run at `pow=16` returned **47,917** perms and
/// another **98,305**, and the 2.05× between them is noise. **A one-sample grind column must
/// never be differenced.** This cell prints the draw, the mean, and the ratio between them so
/// that anyone tempted to difference two grind runs sees the spread first.
#[test]
#[ignore = "measurement rig"]
fn e3_grind_is_a_sample_not_a_measurement() {
    banner("§E3 — GRIND — a draw, not a measurement");
    let mut cond = Conditions::capture(1, false, 1);
    let w = Workload::build(1).expect("workload builds");
    println!("{cond}\n");

    let p0 = Point {
        pow_bits: 0,
        ..Point::deployed()
    };
    let grindless = count_arm(&w, p0).expect("pow=0 proves").prover_only();
    println!("  grind-free prover perms at {}: {grindless}", p0.label());
    println!(
        "\n  ⚑ Each draw uses a DIFFERENT transfer amount. That is not cosmetic: the grind\n              searches a witness for ONE transcript, so re-proving the SAME workload returns the\n              SAME witness and would report a spread of 1.00× — which reads as 'grind is stable',\n              the exact opposite of the truth. Varying the amount varies the trace, the commitment,\n              the challenge, and therefore the draw.\n"
    );

    let p16 = Point {
        pow_bits: 16,
        ..Point::deployed()
    };
    let mut draws = Vec::new();
    for (i, amount) in [50u64, 51, 52, 53, 54, 55].into_iter().enumerate() {
        let wi = Workload::build_with(1, amount).expect("workload builds");
        // The grind-free baseline is amount-independent (same shape), but recompute it per
        // workload rather than assume — assuming is how a censored sample gets fitted.
        let base_i = count_arm(&wi, p0).expect("pow=0 proves").prover_only();
        let c = count_arm(&wi, p16).expect("pow=16 proves");
        let g = c.prover_only().saturating_sub(base_i);
        draws.push(g);
        println!(
            "  draw {i} (amount {amount}): grind = {g:>9} perms   (expectation 2^16 = 65,536)"
        );
    }
    cond.close();

    let lo = *draws.iter().min().unwrap();
    let hi = *draws.iter().max().unwrap();
    let mean = draws.iter().sum::<u64>() as f64 / draws.len() as f64;
    println!(
        "\n  min {lo}  ·  max {hi}  ·  mean {mean:.0}  ·  spread {:.2}×  (theory: geometric, \n             mean 2^16 = 65,536; 256 recorded draws gave p50 53,173 / p99 277,677 / max 398,257)",
        hi as f64 / lo.max(1) as f64
    );
    println!(
        "\n  ⚠ A 'speedup' obtained by differencing two grind runs is NOISE unless it exceeds\n              this spread. Grind must be composed at its MEAN (2^pow), or excluded and NAMED as\n              excluded — a one-sample grind column must never be differenced."
    );
    println!("\n{cond}");
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §F — COMPOSITION
//
// `COST-MODEL.md` rule 4: never compose a work claim with a latency claim. Here that rule is a
// type, not a sentence — `compose()` cannot be called on a mixed set.
// ════════════════════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Claim {
    /// Operations. Exact, composable through the phase model.
    Work,
    /// Critical path. Composable only against other latencies, and only with a scheduler model.
    Latency,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Landed {
    /// In the deployed configuration at HEAD.
    Yes,
    /// The mechanism exists and is tested, but the deployed config does not select it.
    NotCutOver,
}

#[derive(Clone, Debug)]
pub struct Win {
    pub name: &'static str,
    pub phase: &'static str,
    pub claim: Claim,
    pub landed: Landed,
    /// The measured factor, in the unit named by `claim`.
    pub factor: f64,
    pub config: &'static str,
}

/// ⚑ Composing a set of wins. **Refuses** a mixed-unit set, and refuses to count a win that is
/// not actually selected by the deployed configuration.
///
/// This is the whole lesson of `COST-MODEL.md` in one function: the wins do not multiply, they
/// compose through phase shares; and two of them are not in the same unit, so no arithmetic
/// relates them at all.
pub fn compose(wins: &[Win], shares: &BTreeMap<&str, f64>) -> Result<String, String> {
    let units: Vec<Claim> = {
        let mut u: Vec<Claim> = wins.iter().map(|w| w.claim).collect();
        u.dedup();
        u
    };
    if units.len() > 1 {
        return Err(format!(
            "REFUSED — this set mixes {} WORK claims with {} LATENCY claims. Work and latency are \
             different quantities and no arithmetic relates them; composing them is the error \
             COST-MODEL.md rule 4 exists to prevent. Split the set and report two columns.",
            wins.iter().filter(|w| w.claim == Claim::Work).count(),
            wins.iter().filter(|w| w.claim == Claim::Latency).count()
        ));
    }
    let mut out = String::new();
    // Amdahl through the phase shares: a win of factor f on a phase of share s leaves
    // s/f + (1-s). Applied in sequence, re-normalising the shares each time — which is why
    // ORDER MATTERS and multiplying is wrong.
    let mut shares = shares.clone();
    let mut total = 1.0f64;
    for w in wins {
        if w.landed == Landed::NotCutOver {
            writeln!(
                out,
                "  SKIPPED  {:<22} — mechanism exists but the deployed config does not select it",
                w.name
            )
            .ok();
            continue;
        }
        let s = *shares.get(w.phase).unwrap_or(&0.0);
        if s == 0.0 {
            writeln!(
                out,
                "  SKIPPED  {:<22} — phase '{}' carries no share in this model",
                w.name, w.phase
            )
            .ok();
            continue;
        }
        let after = s / w.factor + (1.0 - s);
        writeln!(
            out,
            "  applied  {:<22} phase '{}' share {:.1}% × {:.3}×  ⇒ system {:.4}×   [{}]",
            w.name,
            w.phase,
            s * 100.0,
            w.factor,
            1.0 / after,
            w.config
        )
        .ok();
        total *= 1.0 / after;
        // Re-normalise: the shrunken phase is now a smaller fraction of a smaller whole.
        let scale = 1.0 / after;
        for (k, v) in shares.iter_mut() {
            *v = if *k == w.phase {
                (s / w.factor) * scale
            } else {
                *v * scale
            };
        }
    }
    writeln!(out, "  ── composed: {total:.4}× ──").ok();
    Ok(out)
}

/// **§F — what the four landed wins actually give together.**
///
/// Nobody has done this honestly. Doing it honestly turns out to produce a *refusal* and a
/// finding, not a number — which is the result.
#[test]
#[ignore = "measurement rig"]
fn f_compose_the_four_wins() {
    banner("§F — COMPOSING THE FOUR WINS");

    let wins = vec![
        Win {
            name: "LDE layout",
            phase: "LDE",
            claim: Claim::Latency,
            landed: Landed::Yes,
            factor: 3.66,
            config: "b=6,q=19,pow=0,T=1,min-of-5 — phase ratio",
        },
        Win {
            name: "grind schedule",
            phase: "grind",
            claim: Claim::Latency,
            landed: Landed::Yes,
            factor: 10.6,
            config: "pow=16,T=12,512 draws — DERIVED; counted at T=12 is 7.10×",
        },
        Win {
            name: "blowup drop 6→2",
            phase: "Merkle-commit",
            claim: Claim::Work,
            landed: Landed::NotCutOver,
            factor: 15.19,
            config: "(6,19,p0)→(2,57,p0) — IR2_FRI_LOG_BLOWUP is still 6",
        },
        Win {
            name: "permEmissionNarrow",
            phase: "Merkle-commit",
            claim: Claim::Work,
            landed: Landed::NotCutOver,
            factor: 1.0763,
            config: "per-batch; CHIP_WIDTH is still 386",
        },
    ];

    println!("  The four, with their units and their landed state:\n");
    println!(
        "  {:<22} {:<15} {:<9} {:<14} {:>9}",
        "win", "phase", "unit", "landed", "factor"
    );
    for w in &wins {
        println!(
            "  {:<22} {:<15} {:<9} {:<14} {:>8.3}×",
            w.name,
            w.phase,
            match w.claim {
                Claim::Work => "WORK",
                Claim::Latency => "LATENCY",
            },
            match w.landed {
                Landed::Yes => "yes",
                Landed::NotCutOver => "NOT CUT OVER",
            },
            w.factor
        );
    }

    println!("\n  ── composing all four ──");
    let shares = BTreeMap::new();
    match compose(&wins, &shares) {
        Ok(s) => panic!("all four composed without complaint, which cannot be right:\n{s}"),
        Err(e) => println!("  {e}"),
    }

    // The work column, alone. Both members are not cut over, so it is empty.
    println!("\n  ── the WORK column ──");
    let work: Vec<Win> = wins
        .iter()
        .filter(|w| w.claim == Claim::Work)
        .cloned()
        .collect();
    // Shares are permutation counts at the deployed point, pow=0: Merkle 211,965 of 217,114.
    let mut ws = BTreeMap::new();
    ws.insert("Merkle-commit", 211_965.0 / 217_114.0);
    ws.insert("LDE", 0.0);
    println!(
        "  phase set = prover Poseidon2 permutations at (lb 6, q 19, pow 0) = 217,114; \
         Merkle-commit = 211,965 = 97.6%"
    );
    print!("{}", compose(&work, &ws).expect("work column is one unit"));

    println!("\n  ── the LATENCY column ──");
    let lat: Vec<Win> = wins
        .iter()
        .filter(|w| w.claim == Claim::Latency)
        .cloned()
        .collect();
    let mut ls = BTreeMap::new();
    // Wall-clock shares at b=6, pow=16, from phase-profile.md §2 — a CONTENDED laptop, and the
    // pre-LDE-batching run at that. They are here to show the SHAPE of the composition; the
    // absolute composed number inherits every defect of that measurement and is not a result.
    ls.insert("LDE", 20.6 / 84.9);
    ls.insert("grind", 12.8 / 84.9);
    println!(
        "  phase set = prove wall clock at (lb 6, q 19, pow 16), phase-profile.md §2 \
         — ⚠ CONTENDED LAPTOP, PRE-BATCHING. Shape only."
    );
    print!(
        "{}",
        compose(&lat, &ls).expect("latency column is one unit")
    );

    banner("§F — THE FINDING");
    println!(
        "  Of the four:
    · the two that are LANDED (LDE layout, grind schedule) are both LATENCY claims;
    · the two that carry WORK claims (blowup drop, permEmissionNarrow) are NOT CUT OVER
      — IR2_FRI_LOG_BLOWUP is still 6 and CHIP_WIDTH is still 386.

  So the honest composed answer to 'what do the four landed wins give together' is:
    · in WORK  — nothing. Zero landed wins reduce the operation count. The grind schedule
      RAISES it by +12.6%, and raises grind's share of prover work 23.2% → 25.4%.
    · in LATENCY — the two landed wins compose through the phase model to the figure above,
      on a phase share measured on a contended laptop, pre-batching. Shape, not magnitude.

  The two columns cannot be added, and there is no configuration of this repo at HEAD in which
  a user gets both."
    );
}

// ── the red-capability proof ────────────────────────────────────────────────────────────────

/// ⚑ **Proving the self-check can go red.** A gate nobody has seen fail is a gate nobody has
/// tested. This is a plain unit test — it runs in CI, needs no prover, and fails if the checker
/// ever becomes unfalsifiable.
#[test]
fn self_check_is_red_capable() {
    // Green on the recorded truth.
    let truth: Vec<(usize, u64)> = PINNED_RUNGS.to_vec();
    assert!(
        !self_check(&truth, PINNED_LAW).is_red(),
        "the recorded rungs must pass: {}",
        self_check(&truth, PINNED_LAW).text()
    );

    // (1) SHAPE — a column that is not affine in 2^b.
    let bent = vec![(3usize, 27_778u64), (4, 54_826), (5, 108_925)];
    let r = self_check(&bent, PINNED_LAW);
    assert!(r.is_red(), "a bent column must go red");
    assert!(r.text().contains("PREDICTION"), "got: {}", r.text());

    // (2) PREDICTION — one rung perturbed by a single permutation. The finest possible change.
    let mut one_off = truth.clone();
    one_off[4].1 += 1;
    let r = self_check(&one_off, PINNED_LAW);
    assert!(r.is_red(), "a single-permutation drift at b=7 must go red");

    // (3) PIN — a perfectly affine column with different constants. This is the case that
    // matters most: the prover still works, the shape is intact, and the number has silently
    // stopped being comparable. Simulate one extra committed column's worth of Merkle work.
    let moved = PermLaw { a: 3400, c: 730 };
    let shifted: Vec<(usize, u64)> = (3..=7).map(|b| (b, moved.eval(b))).collect();
    let r = self_check(&shifted, PINNED_LAW);
    assert!(r.is_red(), "a shifted-but-affine column must go red");
    assert!(r.text().contains("PIN"), "got: {}", r.text());
    assert!(
        r.text().contains("3400"),
        "the red must name the new constant"
    );

    // And the checker refuses to be a definition rather than a check.
    assert!(
        self_check(&truth[..2], PINNED_LAW).is_red(),
        "2 rungs is a fit, not a check"
    );

    // The DFT census goes red when the slow path appears.
    let slow = vec![DftShape {
        call: "coset_idft_batch",
        height: 64,
        width: 4,
        added_bits: 0,
    }];
    assert!(dft_census_check(&slow).is_red(), "slow path must go red");
    assert!(!dft_census_check(&[]).is_red());

    // compose() refuses a mixed set.
    let mixed = vec![
        Win {
            name: "w",
            phase: "p",
            claim: Claim::Work,
            landed: Landed::Yes,
            factor: 2.0,
            config: "",
        },
        Win {
            name: "l",
            phase: "p",
            claim: Claim::Latency,
            landed: Landed::Yes,
            factor: 2.0,
            config: "",
        },
    ];
    assert!(
        compose(&mixed, &BTreeMap::new()).is_err(),
        "composing work with latency must be refused"
    );
}

/// The law's decomposition is arithmetic, not numerology: `a` is Merkle + FRI-fold and `c` is
/// the challenger less the two Merkle roots. Asserting it keeps the docblock honest.
#[test]
fn pinned_law_decomposes_into_named_phases() {
    const MERKLE_A: u64 = 3312;
    const FRI_FOLD_A: u64 = 69;
    const CHALLENGER: u64 = 736;
    /// FRI-commit-other (3) + query/open (3) + prove residual (30) — prover permutations that
    /// the three named phases do not span. Constant in `b`, independently recorded at b=3 and
    /// b=6 by `notes/blowup-drop.md`.
    const UNSPANNED: u64 = 36;

    assert_eq!(PINNED_LAW.a, MERKLE_A + FRI_FOLD_A);
    assert_eq!(NAMED_PHASES_LAW.c, CHALLENGER - 3 - 3);
    assert_eq!(PINNED_LAW.c, NAMED_PHASES_LAW.c + UNSPANNED);
    assert_eq!(
        PINNED_LAW.a, NAMED_PHASES_LAW.a,
        "only the intercept differs"
    );

    // The sibling convention reproduces ITS recorded column, which is what makes the 36 a
    // decomposition rather than a fudge factor.
    for (b, want) in [
        (3usize, 27_778u64),
        (4, 54_826),
        (5, 108_922),
        (6, 217_114),
        (7, 433_498),
    ] {
        assert_eq!(
            NAMED_PHASES_LAW.eval(b),
            want,
            "named-phases column at b={b}"
        );
    }
    // And the two rungs of this rig's own column that are recorded rather than predicted.
    assert_eq!(
        PINNED_LAW.eval(3),
        27_814,
        "blowup-drop.md §D2 records 27,814 at b=3"
    );
    assert_eq!(
        PINNED_LAW.eval(6),
        217_150,
        "blowup-drop.md §D2 records 217,150 at b=6"
    );
    // And each named phase reproduces its own recorded column.
    for (b, want) in [
        (3usize, 26_493u64),
        (4, 52_989),
        (5, 105_981),
        (6, 211_965),
        (7, 423_933),
    ] {
        assert_eq!(
            MERKLE_A * (1u64 << b) - 3,
            want,
            "Merkle-commit column at b={b}"
        );
    }
    for (b, want) in [
        (3usize, 549u64),
        (4, 1_101),
        (5, 2_205),
        (6, 4_413),
        (7, 8_829),
    ] {
        assert_eq!(
            FRI_FOLD_A * (1u64 << b) - 3,
            want,
            "FRI-fold column at b={b}"
        );
    }
    for (b, want) in PINNED_RUNGS {
        assert_eq!(PINNED_LAW.eval(*b), *want, "total at b={b}");
    }
}
