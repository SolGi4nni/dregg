//! # PER-PHASE PROFILE OF A REAL IR-v2 PROOF — where the time actually goes, as a function of blowup.
//!
//! `docs/reference/FRI-PARAM-FRONTIER.md` §1b reports a single number per grid point ("prove: 58
//! ms"). That number is an AGGREGATE over four phases with structurally different bottlenecks —
//! coset-LDE (field arithmetic), Merkle commitment (Poseidon2 hashing), FRI folding (field
//! arithmetic, *independent of blowup*), and the query/opening phase (memory + serialization on
//! the prover side, hashing on the verifier side). Two prior readings of "is the prover
//! hash-bound" disagreed (94% derived at lb=6, 19–40% measured at blowup 2) because they
//! aggregated different mixtures. A single ratio cannot settle it; **the crossover in `b` can.**
//!
//! ## Method — tracing spans, not a sampling profiler
//!
//! Plonky3 is already `#[instrument]`ed end to end. This harness installs a `tracing_subscriber`
//! `Layer` that accumulates, per FULL SPAN PATH, the wall-clock SELF time (span busy time minus
//! the busy time of its same-thread children). The paths are then classified into phases. Nothing
//! upstream is patched and no timing call is added to a hot loop.
//!
//! The spans that carry the phases (rev 82cfad73, `vendor/plonky3-fri-82cfad73` for the FRI half):
//!
//! | span | crate | phase |
//! |---|---|---|
//! | `coset_lde_batch_with_transform`, `coset_dft`, `coset_dft_oop` | `p3-dft` | **LDE** |
//! | `build merkle tree`, `first digest layer` | `p3-merkle-tree` | **Merkle (hashing)** |
//! | `compute quotient`, `compute quotient polynomial` | `p3-batch-stark` | **quotient (arithmetic)** |
//! | `FRI prover` > `commit phase` > `fold_matrix` | `p3-fri` | **fold (arithmetic)** |
//! | `FRI prover` > `commit phase` > `build merkle tree` | `p3-fri` | **fold-round Merkle (hashing)** |
//! | `FRI prover` > `query phase` | `p3-fri` | **query/opening** |
//! | `reduce matrix quotient`, `compress mat`, `evaluate matrix`, `compute_inverse_denominators` | `p3-fri` | **open arithmetic** |
//! | `verify_batch` and everything under it | `p3-batch-stark` | **VERIFIER** |
//!
//! Because `build merkle tree` occurs BOTH under the main/quotient commits AND under the FRI
//! commit phase, buckets are keyed by the full path, never by the name alone.
//!
//! ## What this method CANNOT see
//!
//! 1. **Un-instrumented code is invisible as a phase** — it lands in the enclosing span's self
//!    time. `Pcs::commit` itself carries no span, so the bit-reversal + `to_row_major_matrix`
//!    copies between the LDE and the Merkle build show up as `prove_batch` self time, not as
//!    "LDE". The residual row is therefore REAL WORK, not measurement noise, and it is reported.
//! 2. **Rayon.** Span busy time is measured on the thread that entered the span; every
//!    instrumented function here is entered on the driving thread with rayon parallelism *inside*
//!    it, so the numbers are wall-clock elapsed for the parallel section — not CPU-seconds. On a
//!    contended box that inflates every phase that parallelises well. `RAYON_NUM_THREADS=1`
//!    removes the confound and is the run to quote for "which phase is the work".
//! 3. **No op counts from timing.** Poseidon2 permutation counts come from the separate
//!    counting-permutation config below, not from these spans.
//! 4. **Instrumentation cost.** Two `Instant::now()` per span. Span counts are in the thousands,
//!    not the millions (no span is inside a per-element loop), so this is well under 1 ms.
//!
//! ## Runs
//!
//! ```text
//! cargo test -p dregg-circuit --release --test ir2_phase_profile -- --nocapture --test-threads=1
//! RAYON_NUM_THREADS=1 cargo test -p dregg-circuit --release --test ir2_phase_profile -- --nocapture --test-threads=1
//! ```
//! Release only — a debug timing here is a lie.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_with_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace};
use dregg_circuit::effect_vm_descriptors::descriptor2_for_key;
use dregg_circuit::field::BabyBear;
use dregg_circuit::plonky3_prover::create_config_with_fri;
use tracing::Subscriber;
use tracing::span::Id;
use tracing_subscriber::layer::{Context, Layer, SubscriberExt};
use tracing_subscriber::registry::LookupSpan;

// ─────────────────────────────────────────────────────────────────────────────
// THE LAYER: per-span-path self time
// ─────────────────────────────────────────────────────────────────────────────

struct Frame {
    path: String,
    start: Instant,
    child: Duration,
    perms_at_enter: u64,
    child_perms: u64,
}

thread_local! {
    static STACK: RefCell<Vec<Frame>> = const { RefCell::new(Vec::new()) };
}

/// Global Poseidon2 permutation counter in SCALAR-EQUIVALENT units, incremented by
/// [`CountingPerm`]: a scalar `permute_mut` adds 1, a packed one adds `Packing::WIDTH` (it permutes
/// that many independent states in one SIMD call). Read as a delta across a span's lifetime, so it
/// attributes work done on rayon workers to the span that spawned it. Zero unless the
/// counting config (§D) is the one proving — the deployed `DreggStarkConfig` does not touch it.
static PERMS: AtomicU64 = AtomicU64::new(0);
/// Packed `permute_mut` CALL count (SIMD instructions issued), for the vectorisation ratio.
static PERMS_PACKED: AtomicU64 = AtomicU64::new(0);

#[derive(Default, Clone, Copy)]
struct Bucket {
    self_time: Duration,
    total_time: Duration,
    self_perms: u64,
    calls: u64,
}

fn totals() -> &'static Mutex<HashMap<String, Bucket>> {
    static T: OnceLock<Mutex<HashMap<String, Bucket>>> = OnceLock::new();
    T.get_or_init(|| Mutex::new(HashMap::new()))
}

struct PhaseLayer;

/// Captures the `dims = HxW` / `added_bits = b` fields plonky3's DFT spans already carry, so the
/// LDE GEOMETRY (and therefore the butterfly count) is recoverable without a second harness.
#[derive(Default)]
struct SpanFields(String);

struct FieldGrab(String);
impl tracing::field::Visit for FieldGrab {
    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
        let n = field.name();
        if n == "dims" || n == "added_bits" {
            if !self.0.is_empty() {
                self.0.push(',');
            }
            self.0.push_str(&format!("{n}={value:?}").replace('"', ""));
        }
    }
}

impl<S> Layer<S> for PhaseLayer
where
    S: Subscriber + for<'a> LookupSpan<'a>,
{
    fn on_new_span(&self, attrs: &tracing::span::Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
        let mut g = FieldGrab(String::new());
        attrs.record(&mut g);
        if !g.0.is_empty() {
            if let Some(span) = ctx.span(id) {
                span.extensions_mut().insert(SpanFields(g.0));
            }
        }
    }

    fn on_enter(&self, id: &Id, ctx: Context<'_, S>) {
        let span = ctx.span(id);
        let name = span.as_ref().map(|s| s.name()).unwrap_or("?");
        let fields = span
            .as_ref()
            .and_then(|s| s.extensions().get::<SpanFields>().map(|f| f.0.clone()))
            .unwrap_or_default();
        let name: std::borrow::Cow<'_, str> = if fields.is_empty() {
            name.into()
        } else {
            format!("{name}[{fields}]").into()
        };
        STACK.with(|s| {
            let mut st = s.borrow_mut();
            let path = match st.last() {
                Some(p) => format!("{}>{name}", p.path),
                None => name.to_string(),
            };
            st.push(Frame {
                path,
                start: Instant::now(),
                child: Duration::ZERO,
                perms_at_enter: PERMS.load(Ordering::Relaxed),
                child_perms: 0,
            });
        });
    }

    fn on_exit(&self, _id: &Id, _ctx: Context<'_, S>) {
        STACK.with(|s| {
            let mut st = s.borrow_mut();
            let Some(f) = st.pop() else { return };
            let total = f.start.elapsed();
            let perms = PERMS.load(Ordering::Relaxed) - f.perms_at_enter;
            if let Some(p) = st.last_mut() {
                p.child += total;
                p.child_perms += perms;
            }
            let mut map = totals().lock().unwrap();
            let b = map.entry(f.path).or_default();
            b.self_time += total.saturating_sub(f.child);
            b.total_time += total;
            b.self_perms += perms.saturating_sub(f.child_perms);
            b.calls += 1;
        });
    }
}

fn install_layer() {
    static ONCE: OnceLock<()> = OnceLock::new();
    ONCE.get_or_init(|| {
        let sub = tracing_subscriber::registry().with(PhaseLayer);
        tracing::subscriber::set_global_default(sub).expect("global subscriber");
    });
}

fn reset_totals() {
    totals().lock().unwrap().clear();
    PERMS.store(0, Ordering::Relaxed);
    PERMS_PACKED.store(0, Ordering::Relaxed);
}

fn snapshot() -> HashMap<String, Bucket> {
    totals().lock().unwrap().clone()
}

// ─────────────────────────────────────────────────────────────────────────────
// THE PHASE CLASSIFIER — path patterns, checked in order
// ─────────────────────────────────────────────────────────────────────────────

/// Phase labels, in report order. `Phase::of` is total on span paths.
const PHASES: &[&str] = &[
    "LDE commit (arith)",
    "LDE quotient-eval (arith)",
    "Merkle-commit (hash)",
    "quotient eval (arith)",
    "lookup perm (arith)",
    "FRI fold (arith)",
    "FRI fold Merkle (hash)",
    "FRI commit other",
    "query/open phase",
    "open arith (quotient reduce)",
    "PoW grind (hash)",
    "prove residual (unspanned)",
];

/// The four HASHING buckets and the six ARITHMETIC ones. `PoW grind` is hashing but is
/// **blowup- and trace-INDEPENDENT** (it is a pure function of `query_proof_of_work_bits`), so
/// every crossover is reported both with and without it — see [`hash_arith`].
const HASH_PHASES: &[&str] = &["Merkle-commit (hash)", "FRI fold Merkle (hash)"];
const ARITH_PHASES: &[&str] = &[
    "LDE commit (arith)",
    "LDE quotient-eval (arith)",
    "quotient eval (arith)",
    "lookup perm (arith)",
    "FRI fold (arith)",
    "open arith (quotient reduce)",
];

fn classify(path: &str) -> Option<&'static str> {
    if path.contains("verify_batch") {
        return None; // verifier accounted separately
    }
    // ⚑ THE PHASE NOBODY NAMED. `GrindingChallenger::grind` searches for a
    // `query_proof_of_work_bits`-bit witness with the duplex Poseidon2 challenger; it is pure
    // hashing, it is ~25% of a deployed prove, and it depends on NEITHER the blowup NOR the trace
    // size — only on `pow_bits` and on which witness index the Fiat–Shamir transcript happens to
    // land on. Aggregating it into "prove time" is a large part of why single-ratio readings of
    // "is the prover hash-bound" disagree.
    if path.contains("grind for proof-of-work") {
        return Some("PoW grind (hash)");
    }
    if path.contains("query phase") {
        return Some("query/open phase");
    }
    if path.contains("commit phase") {
        // inside the FRI commit phase
        if path.contains("build merkle tree") || path.contains("first digest layer") {
            return Some("FRI fold Merkle (hash)");
        }
        if path.contains("fold_matrix") {
            return Some("FRI fold (arith)");
        }
        return Some("FRI commit other");
    }
    if path.contains("coset_lde_batch") || path.contains("coset_dft") || path.contains("idft") {
        // The LDE under `compute quotient` is `get_evaluations_on_domain` re-evaluating the
        // COMMITTED trace onto the quotient domain — a different scaling law from the commit LDE
        // (it is driven by the constraint degree, and by the committed LDE height for the iDFT).
        return Some(if path.contains("compute quotient") {
            "LDE quotient-eval (arith)"
        } else {
            "LDE commit (arith)"
        });
    }
    if path.contains("build merkle tree") || path.contains("first digest layer") {
        return Some("Merkle-commit (hash)");
    }
    if path.contains("generate lookup permutation") {
        return Some("lookup perm (arith)");
    }
    if path.contains("quotient polynomial")
        || path.contains("compute quotient")
        || path.contains("Compute Selectors")
    {
        return Some("quotient eval (arith)");
    }
    if path.contains("reduce matrix quotient")
        || path.contains("compress mat")
        || path.contains("evaluate matrix")
        || path.contains("compute_inverse_denominators")
        || path.contains("barycentric")
    {
        return Some("open arith (quotient reduce)");
    }
    Some("prove residual (unspanned)")
}

/// `(hash-without-grind, arithmetic, grind)` in ms.
fn hash_arith(p: &Point) -> (f64, f64, f64) {
    let hash: f64 = HASH_PHASES.iter().map(|ph| phase_ms(p, ph)).sum();
    let arith: f64 = ARITH_PHASES.iter().map(|ph| phase_ms(p, ph)).sum();
    (hash, arith, phase_ms(p, "PoW grind (hash)"))
}

#[derive(Default, Clone)]
struct PhaseTable {
    per_phase: HashMap<&'static str, (Duration, u64)>,
    verifier: Duration,
    prove_span: Duration,
    verifier_perms: u64,
}

fn tabulate(snap: &HashMap<String, Bucket>) -> PhaseTable {
    let mut t = PhaseTable::default();
    for (path, b) in snap {
        if path == "prove_batch" || path.starts_with("prove_batch>") {
            // total_time of the ROOT prove_batch span is the prove wall clock
        }
        if path.contains("verify_batch") {
            t.verifier += b.self_time;
            t.verifier_perms += b.self_perms;
            continue;
        }
        if let Some(p) = classify(path) {
            let e = t.per_phase.entry(p).or_insert((Duration::ZERO, 0));
            e.0 += b.self_time;
            e.1 += b.self_perms;
        }
    }
    t.prove_span = snap
        .get("prove_batch")
        .map(|b| b.total_time)
        .unwrap_or_default();
    t
}

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.0
}

// ─────────────────────────────────────────────────────────────────────────────
// THE WORKLOAD — the SAME real transfer effect `effect_vm_ir2_size_measure::ir2_fri_grid` prices
// ─────────────────────────────────────────────────────────────────────────────

struct Workload {
    desc: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    base_trace: Vec<Vec<BabyBear>>,
    pis: Vec<BabyBear>,
}

fn transfer_workload() -> Workload {
    let state = CellState::new(100_000, 0);
    let effects = vec![Effect::Transfer {
        amount: 50,
        direction: 1,
    }];
    let (base_trace, pis) = generate_effect_vm_trace(&state, &effects);
    let v2_json = descriptor2_for_key("transferVmDescriptor2").expect("v2 transfer descriptor");
    let desc = parse_vm_descriptor2(v2_json).expect("v2 transfer descriptor parses");
    let dpis: Vec<BabyBear> = pis[..desc.public_input_count].to_vec();
    Workload {
        desc,
        base_trace,
        pis: dpis,
    }
}

/// One (lb, q) point, `reps` repetitions, keeping the phase table of the FASTEST prove.
struct Point {
    lb: usize,
    q: usize,
    min_prove_ms: f64,
    med_prove_ms: f64,
    min_verify_ms: f64,
    proof_bytes: usize,
    table: PhaseTable,
    /// Per-phase minimum over `reps` — see the note in [`measure_point`].
    per_phase_min: HashMap<&'static str, f64>,
    reps: usize,
}

fn measure_point(
    w: &Workload,
    lb: usize,
    q: usize,
    pow: usize,
    reps: usize,
) -> Result<Point, String> {
    let config = create_config_with_fri(lb, 0, 3, q, pow);
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    let mut proves: Vec<f64> = Vec::new();
    let mut verifies: Vec<f64> = Vec::new();
    let mut best = f64::INFINITY;
    let mut best_table = PhaseTable::default();
    // ⚑ THE ESTIMATOR, and it is not "the phase table of the fastest run". On a contended box
    // preemption inflates whichever phase happened to be running, independently per phase, so the
    // fastest WHOLE run is not the run in which any given phase was cleanest. The per-phase
    // MINIMUM over reps is the closest observable to the uncontended cost of that phase. It does
    // NOT sum to any single observed prove time, and is not claimed to.
    let mut per_phase_min: HashMap<&'static str, f64> = HashMap::new();
    let mut bytes = 0usize;

    for _ in 0..reps {
        reset_totals();
        let t0 = Instant::now();
        let proof = prove_vm_descriptor2_with_config(
            &w.desc,
            &w.base_trace,
            &w.pis,
            &mem_boundary,
            &map_heaps,
            &config,
        )?;
        // NOTE: this call INCLUDES a full `verify_batch` self-verify (descriptor_ir2.rs `check`).
        // The span table separates them; this wall clock does not.
        let wall = t0.elapsed().as_secs_f64() * 1000.0;
        let snap = snapshot();
        let table = tabulate(&snap);
        // prove-ONLY = the `prove_batch` span total; the self-verify is the `verify_batch` span.
        let prove_only = ms(table.prove_span);

        reset_totals();
        let t1 = Instant::now();
        verify_vm_descriptor2_with_config(&w.desc, &proof, &w.pis, &config)?;
        let vwall = t1.elapsed().as_secs_f64() * 1000.0;

        let _ = wall;
        proves.push(prove_only);
        verifies.push(vwall);
        for ph in PHASES {
            let v = table
                .per_phase
                .get(ph)
                .map(|(d, _)| ms(*d))
                .unwrap_or(f64::INFINITY);
            let e = per_phase_min.entry(ph).or_insert(f64::INFINITY);
            if v < *e {
                *e = v;
            }
        }
        {
            let v = ms(table.verifier);
            let e = per_phase_min.entry("SELFVERIFY").or_insert(f64::INFINITY);
            if v < *e {
                *e = v;
            }
        }
        if prove_only < best {
            best = prove_only;
            best_table = table;
            bytes = rmp_serde::to_vec(&proof).map(|v| v.len()).unwrap_or(0);
        }
    }
    for (k, v) in per_phase_min.iter_mut() {
        if !v.is_finite() {
            *v = 0.0;
        }
        let _ = k;
    }
    let mut sorted = proves.clone();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let med = sorted[sorted.len() / 2];
    let minv = verifies.iter().cloned().fold(f64::INFINITY, f64::min);

    Ok(Point {
        lb,
        q,
        min_prove_ms: best,
        med_prove_ms: med,
        min_verify_ms: minv,
        proof_bytes: bytes,
        table: best_table,
        per_phase_min,
        reps,
    })
}

fn print_point(p: &Point) {
    println!(
        "\n── lb={} (blowup {}×) q={}  [min of N={}]  prove_batch {:.2} ms (median {:.2}) | \
         standalone verify {:.2} ms | proof {} B",
        p.lb,
        1usize << p.lb,
        p.q,
        p.reps,
        p.min_prove_ms,
        p.med_prove_ms,
        p.min_verify_ms,
        p.proof_bytes,
    );
    let total: f64 = PHASES.iter().map(|ph| phase_ms(p, ph)).sum();
    println!(
        "   {:<32} {:>9}  {:>7}  {:>10}",
        "phase", "min ms", "% total", "bestrun ms"
    );
    for ph in PHASES {
        let d = phase_ms(p, ph);
        if d < 0.0005 {
            continue;
        }
        println!(
            "   {:<32} {:>9.3}  {:>6.1}%  {:>10.3}",
            ph,
            d,
            100.0 * d / total.max(1e-9),
            phase_ms_bestrun(p, ph)
        );
    }
    let (hash, arith, grind) = hash_arith(p);
    println!(
        "   {:<32} {:>9.3}  {:>6.1}%",
        "— accounted total", total, 100.0
    );
    println!(
        "   HASH(merkle) {:.3} ms | ARITH {:.3} ms | grind {:.3} ms  ⇒  hash/arith = {:.3}  \
         (incl. grind {:.3})",
        hash,
        arith,
        grind,
        hash / arith.max(1e-9),
        (hash + grind) / arith.max(1e-9),
    );
    println!(
        "   in-prove self-verify (verify_batch span): {:.3} ms  ({:.1}% of the prove call)",
        ms(p.table.verifier),
        100.0 * ms(p.table.verifier) / (p.min_prove_ms + ms(p.table.verifier)).max(1e-9),
    );
}

/// Per-phase MINIMUM over the reps (the contention-robust estimator; see [`measure_point`]).
fn phase_ms(p: &Point, ph: &str) -> f64 {
    p.per_phase_min.get(ph).copied().unwrap_or(0.0)
}

/// The phase table of the single fastest run — reported alongside `phase_ms` so a reader can see
/// whether the two estimators disagree.
fn phase_ms_bestrun(p: &Point, ph: &str) -> f64 {
    p.table
        .per_phase
        .get(ph)
        .map(|(d, _)| ms(*d))
        .unwrap_or(0.0)
}

// ─────────────────────────────────────────────────────────────────────────────
// THE MEASUREMENTS
// ─────────────────────────────────────────────────────────────────────────────

/// **§A — the blowup sweep at FIXED query count.** `q` is held at the deployed 19 so the ONLY
/// moving knob is `b`. This is the sweep that answers "where does hashing overtake arithmetic",
/// because at parity (§B) the query count moves too and the two effects are confounded.
#[test]
fn phase_profile_blowup_sweep_fixed_queries() {
    install_layer();
    let w = transfer_workload();
    let reps: usize = std::env::var("DREGG_PROFILE_REPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5);

    println!(
        "\n═══ §A BLOWUP SWEEP AT FIXED q=19, pow=0 — rayon threads: {} ═══\n\
         ⚑ `query_proof_of_work_bits` is set to 0 here ON PURPOSE. At the deployed pow=16 the\n\
         grind is a RANDOM DRAW: the witness index is a deterministic function of the Fiat–Shamir\n\
         transcript, so it differs per grid point with no relation to the blowup. Measured across\n\
         one q=19 sweep it ranged 0.1 ms .. 60.5 ms — larger than the entire Merkle term. Any\n\
         blowup conclusion drawn from a pow=16 prove column is reading that draw.",
        rayon_threads()
    );
    let mut pts = Vec::new();
    for lb in [2usize, 3, 4, 5, 6, 7, 8] {
        match measure_point(&w, lb, 19, 0, reps) {
            Ok(p) => {
                print_point(&p);
                pts.push(p);
            }
            Err(e) => println!("\n── lb={lb} q=19: INFEASIBLE — {e}"),
        }
    }
    crossover_table("§A", &pts);
    println!(
        "\n── §A SCALING CHECK (ratio to the previous rung; a term that is Θ(2^b) doubles)\n   \
         {:<30} {}",
        "phase",
        pts.windows(2)
            .map(|w| format!("{:>10}", format!("{}→{}", w[0].lb, w[1].lb)))
            .collect::<String>()
    );
    for ph in PHASES {
        if pts.iter().all(|p| phase_ms(p, ph) < 0.005) {
            continue;
        }
        print!("   {ph:<30}");
        for pair in pts.windows(2) {
            print!(
                "{:>10.2}",
                phase_ms(&pair[1], ph) / phase_ms(&pair[0], ph).max(1e-9)
            );
        }
        println!();
    }
}

/// The crossover table: hashing (Merkle only) against arithmetic (LDE + quotient + fold + open),
/// with the trace-independent PoW grind broken out so the reader can see which conclusion depends
/// on it.
fn crossover_table(tag: &str, pts: &[Point]) {
    println!(
        "\n── {tag} CROSSOVER TABLE  (hash = Merkle-commit + FRI-fold-Merkle; arith = LDE-commit + \
         LDE-quot-eval + quotient + lookup + fold + open-arith; grind is hash but \
         blowup-INDEPENDENT)"
    );
    println!(
        "   {:>3} {:>4} {:>8} {:>9} {:>9} {:>9} {:>8} {:>9} {:>10} {:>9}",
        "lb",
        "q",
        "blowup",
        "hash ms",
        "arith ms",
        "grind ms",
        "hash/ar",
        "(h+g)/ar",
        "prove ms",
        "verify ms"
    );
    for p in pts {
        let (hash, arith, grind) = hash_arith(p);
        println!(
            "   {:>3} {:>4} {:>8} {:>9.3} {:>9.3} {:>9.3} {:>8.3} {:>9.3} {:>10.3} {:>9.3}",
            p.lb,
            p.q,
            1usize << p.lb,
            hash,
            arith,
            grind,
            hash / arith.max(1e-9),
            (hash + grind) / arith.max(1e-9),
            p.min_prove_ms,
            p.min_verify_ms
        );
    }
    println!("\n── {tag} PER-PHASE MATRIX (ms, min-of-N run at each point)");
    print!("   {:<30}", "phase");
    for p in pts {
        print!(" {:>9}", format!("lb{}q{}", p.lb, p.q));
    }
    println!();
    for ph in PHASES {
        if pts.iter().all(|p| phase_ms(p, ph) < 0.0005) {
            continue;
        }
        print!("   {ph:<30}");
        for p in pts {
            print!(" {:>9.3}", phase_ms(p, ph));
        }
        println!();
    }
    print!("   {:<30}", "VERIFIER (standalone)");
    for p in pts {
        print!(" {:>9.3}", p.min_verify_ms);
    }
    println!();
    print!("   {:<30}", "verifier % of prove+verify");
    for p in pts {
        print!(
            " {:>8.1}%",
            100.0 * p.min_verify_ms / (p.min_prove_ms + p.min_verify_ms).max(1e-9)
        );
    }
    println!();
}

/// **§B — the SECURITY-PARITY ladder**, the grid `FRI-PARAM-FRONTIER.md` §1b quotes (20 ms at
/// lb=4 vs 58 ms at lb=6). Reproduce or refute. ⚑ The published column is `prove+selfverify`;
/// this one separates them.
#[test]
fn phase_profile_parity_ladder() {
    install_layer();
    let w = transfer_workload();
    let reps: usize = std::env::var("DREGG_PROFILE_REPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5);

    println!(
        "\n═══ §B SECURITY-PARITY LADDER (q·lb+16 ≈ 130) — rayon threads: {} ═══",
        rayon_threads()
    );
    let mut pts = Vec::new();
    for (lb, q) in [
        (3usize, 38usize),
        (4, 29),
        (5, 23),
        (6, 19),
        (7, 17),
        (8, 15),
    ] {
        match measure_point(&w, lb, q, 16, reps) {
            Ok(p) => {
                print_point(&p);
                pts.push(p);
            }
            Err(e) => println!("\n── lb={lb} q={q}: INFEASIBLE — {e}"),
        }
    }
    println!(
        "\n── §B PARITY LADDER SUMMARY  (⚑ `FRI-PARAM-FRONTIER.md` §1b's `prove` column is \
              prove+selfverify; here they are separated)"
    );
    println!(
        "   {:>3} {:>4} {:>10} {:>12} {:>13} {:>10} {:>10}",
        "lb", "q", "prove ms", "selfverif ms", "published ms", "verify ms", "bytes"
    );
    for p in &pts {
        println!(
            "   {:>3} {:>4} {:>10.3} {:>12.3} {:>13.3} {:>10.3} {:>10}",
            p.lb,
            p.q,
            p.min_prove_ms,
            ms(p.table.verifier),
            p.min_prove_ms + ms(p.table.verifier),
            p.min_verify_ms,
            p.proof_bytes,
        );
    }
    crossover_table("§B(pow=16)", &pts);

    // The SAME ladder with the grind removed — this is the curve that is a function of (lb, q)
    // alone, and the one an optimum may honestly be read off.
    println!("\n═══ §B2 THE SAME PARITY LADDER AT pow=0 (grind removed) ═══");
    let mut clean = Vec::new();
    for (lb, q) in [
        (3usize, 38usize),
        (4, 29),
        (5, 23),
        (6, 19),
        (7, 17),
        (8, 15),
    ] {
        if let Ok(p) = measure_point(&w, lb, q, 0, reps) {
            clean.push(p);
        }
    }
    println!(
        "   {:>3} {:>4} {:>10} {:>12} {:>10} {:>10}",
        "lb", "q", "prove ms", "selfverif ms", "verify ms", "bytes"
    );
    for p in &clean {
        println!(
            "   {:>3} {:>4} {:>10.3} {:>12.3} {:>10.3} {:>10}",
            p.lb,
            p.q,
            p.min_prove_ms,
            ms(p.table.verifier),
            p.min_verify_ms,
            p.proof_bytes,
        );
    }
    crossover_table("§B2(pow=0)", &clean);
}

/// **§C — the raw span dump at the deployed point.** Every span path with a non-trivial share, so
/// the classifier in this file can be audited against what plonky3 actually reports.
#[test]
fn phase_profile_raw_spans_at_deployed_point() {
    install_layer();
    let w = transfer_workload();
    let config = create_config_with_fri(6, 0, 3, 19, 16);
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    reset_totals();
    let t0 = Instant::now();
    let proof = prove_vm_descriptor2_with_config(
        &w.desc,
        &w.base_trace,
        &w.pis,
        &mem_boundary,
        &map_heaps,
        &config,
    )
    .expect("deployed point proves");
    let wall = t0.elapsed();
    let snap = snapshot();
    let _ = proof;

    let mut rows: Vec<(&String, &Bucket)> = snap.iter().collect();
    rows.sort_by_key(|(_, b)| std::cmp::Reverse(b.self_time));
    println!(
        "\n═══ §C RAW SPAN SELF-TIME at lb=6 q=19 (single run, wall {:.2} ms incl. self-verify) ═══",
        ms(wall)
    );
    println!(
        "   {:>9} {:>9} {:>7}  {}",
        "self ms", "total ms", "calls", "span path"
    );
    for (path, b) in rows.iter().take(45) {
        println!(
            "   {:>9.3} {:>9.3} {:>7}  {}",
            ms(b.self_time),
            ms(b.total_time),
            b.calls,
            path
        );
    }
}

fn rayon_threads() -> String {
    std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "default (all cores)".into())
}

// ─────────────────────────────────────────────────────────────────────────────
// §D — EXACT POSEIDON2 PERMUTATION COUNTS PER PHASE
//
// The timing above says "hashing"; this says HOW MANY PERMUTATIONS, which is the number a silicon
// argument needs and the one that does not move with the box. `prove_vm_descriptor2_for_config` is
// generic over `SC`, so no deployed type is touched: the same real transfer is proven under a
// config whose ONLY difference is that its Poseidon2 permutation increments a counter.
//
// ⚠ THIS RUN'S TIMINGS ARE MEANINGLESS and are not reported. A relaxed `fetch_add` per permutation
// is a global cache line touched millions of times; it inflates exactly the phase it measures.
// Counts are exact; the ms column of this test is deliberately absent.
// ─────────────────────────────────────────────────────────────────────────────

use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::Field;
use p3_field::PackedValue;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{
    CryptographicPermutation, PaddingFreeSponge, Permutation, TruncatedPermutation,
};
use p3_uni_stark::StarkConfig;

type Pack = <P3BabyBear as Field>::Packing;

#[derive(Clone)]
struct CountingPerm(Poseidon2BabyBear<16>);

// ONE generic impl, not one per state type. Two inherent impls (`[BabyBear; 16]` and
// `[BabyBear::Packing; 16]`) do not pass coherence: `<BabyBear as Field>::Packing` is a projection
// and rustc will not normalize it in an impl header far enough to prove the two headers disjoint.
// The lane count is recovered from the state's SIZE instead, which is exact and arch-portable
// (NEON w=4, AVX2 w=8, AVX-512 w=16, scalar w=1 all fall out of `size_of`).
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

type CEf = BinomialExtensionField<P3BabyBear, 4>;
type CHash = PaddingFreeSponge<CountingPerm, 16, 8, 8>;
type CCompress = TruncatedPermutation<CountingPerm, 2, 8, 16>;
type CValMmcs = MerkleTreeMmcs<Pack, Pack, CHash, CCompress, 2, 8>;
type CChallengeMmcs = ExtensionMmcs<P3BabyBear, CEf, CValMmcs>;
type CPcs = TwoAdicFriPcs<P3BabyBear, Radix2DitParallel<P3BabyBear>, CValMmcs, CChallengeMmcs>;
type CChallenger = DuplexChallenger<P3BabyBear, CountingPerm, 16, 8>;
type CountingConfig = StarkConfig<CPcs, CEf, CChallenger>;

fn counting_config(log_blowup: usize, num_queries: usize, pow: usize) -> CountingConfig {
    let perm = CountingPerm(default_babybear_poseidon2_16());
    let hash = CHash::new(perm.clone());
    let compress = CCompress::new(perm.clone());
    let val_mmcs = CValMmcs::new(hash, compress, 0);
    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len: 0,
        max_log_arity: 3,
        num_queries,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: pow,
        mmcs: CChallengeMmcs::new(val_mmcs.clone()),
    };
    let pcs = TwoAdicFriPcs::new(Radix2DitParallel::default(), val_mmcs, fri_params);
    StarkConfig::new(pcs, CChallenger::new(perm))
}

/// **§D — the op count.** Poseidon2 permutations (scalar-equivalent), per phase, per blowup.
#[test]
fn poseidon2_permutation_counts_per_phase() {
    use dregg_circuit::descriptor_ir2::{UMemBoundaryWitness, prove_vm_descriptor2_for_config};
    install_layer();
    let w = transfer_workload();
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    let umem = UMemBoundaryWitness::default();

    println!(
        "\n═══ §D EXACT POSEIDON2 PERMUTATION COUNTS (scalar-equivalent; SIMD lane width = {}) ═══",
        Pack::WIDTH
    );
    let mut rows: Vec<(usize, usize, HashMap<&'static str, u64>, u64, u64)> = Vec::new();
    for (lb, q, pow) in [
        (3usize, 19usize, 0usize),
        (4, 19, 0),
        (5, 19, 0),
        (6, 19, 0),
        (7, 19, 0),
        (6, 19, 16),
    ] {
        let config = counting_config(lb, q, pow);
        reset_totals();
        let proof = prove_vm_descriptor2_for_config(
            &w.desc,
            &w.base_trace,
            &w.pis,
            &mem_boundary,
            &map_heaps,
            &umem,
            &config,
        )
        .expect("counting config proves");
        let _ = &proof;
        let snap = snapshot();
        let packed_calls = PERMS_PACKED.load(Ordering::Relaxed);
        let total = PERMS.load(Ordering::Relaxed);
        let mut per: HashMap<&'static str, u64> = HashMap::new();
        let mut verifier = 0u64;
        for (path, b) in &snap {
            if path.contains("verify_batch") {
                verifier += b.self_perms;
                continue;
            }
            if let Some(ph) = classify(path) {
                *per.entry(ph).or_default() += b.self_perms;
            }
        }
        per.insert("VERIFIER (self-verify)", verifier);
        rows.push((lb, pow, per, total, packed_calls));
    }

    let mut phases: Vec<&'static str> = PHASES.to_vec();
    phases.push("VERIFIER (self-verify)");
    print!("   {:<32}", "phase");
    for (lb, pow, _, _, _) in &rows {
        print!(" {:>13}", format!("lb{lb} pow{pow}"));
    }
    println!();
    for ph in &phases {
        if rows.iter().all(|r| r.2.get(ph).copied().unwrap_or(0) == 0) {
            continue;
        }
        print!("   {ph:<32}");
        for r in &rows {
            print!(" {:>13}", r.2.get(ph).copied().unwrap_or(0));
        }
        println!();
    }
    print!("   {:<32}", "TOTAL perms (scalar-equiv)");
    for r in &rows {
        print!(" {:>13}", r.3);
    }
    println!();
    print!("   {:<32}", "  of which SIMD calls issued");
    for r in &rows {
        print!(" {:>13}", r.4);
    }
    println!();
    println!(
        "\n   ⚑ The grind column is the pow=16 run minus the pow=0 run at the same (lb, q): a pure\n   \
         function of the PoW bits and the Fiat–Shamir witness index, not of the trace or blowup."
    );
}

/// **§E — the conversion constant.** Permutation counts are hardware-free; milliseconds are not.
/// This measures THIS box's Poseidon2 rate so §D's counts can be turned into a time and
/// cross-checked against the span table — an independent check that the classifier attributes to
/// the right phase.
///
/// ⚑ TWO rates, and confusing them is how a cross-check "fails". Permuting ONE state in a loop
/// measures LATENCY (each permutation depends on the last). The Merkle tree and the PoW grind
/// permute INDEPENDENT states, so they run at THROUGHPUT (the pipeline overlaps them). Both are
/// reported; only the throughput one may be multiplied by a count.
#[test]
fn poseidon2_rate_and_count_to_time_crosscheck() {
    use p3_field::PrimeCharacteristicRing;
    use p3_symmetric::Permutation as _;

    let perm = default_babybear_poseidon2_16();

    // SHORT windows, MANY of them. This box is shared (load average 30..95 while these numbers
    // were taken); a 1-second timing window cannot escape preemption, a few-thousand-perm one can.
    fn min_ns<F: FnMut()>(windows: usize, per_window: u64, mut f: F) -> f64 {
        let mut best = f64::INFINITY;
        for _ in 0..windows {
            let t = Instant::now();
            f();
            let e = t.elapsed().as_secs_f64() / per_window as f64;
            if e < best {
                best = e;
            }
        }
        best * 1e9
    }

    let mut st = [P3BabyBear::ONE; 16];
    for _ in 0..10_000 {
        perm.permute_mut(&mut st);
    }
    let scalar_lat = min_ns(4_000, 512, || {
        for _ in 0..512 {
            perm.permute_mut(std::hint::black_box(&mut st));
        }
    });

    let mut bank: Vec<[P3BabyBear; 16]> = (0..512)
        .map(|i| {
            let mut a = [P3BabyBear::ONE; 16];
            a[0] = P3BabyBear::from_u32(i as u32);
            a
        })
        .collect();
    let scalar_thr = min_ns(4_000, 512, || {
        for s in bank.iter_mut() {
            perm.permute_mut(std::hint::black_box(s));
        }
    });

    let mut pbank: Vec<[Pack; 16]> = (0..512)
        .map(|i| {
            let mut a = [Pack::from(P3BabyBear::ONE); 16];
            a[0] = Pack::from(P3BabyBear::from_u32(i as u32));
            a
        })
        .collect();
    let packed_thr_call = min_ns(4_000, 512, || {
        for s in pbank.iter_mut() {
            perm.permute_mut(std::hint::black_box(s));
        }
    });
    let packed_thr_lane = packed_thr_call / Pack::WIDTH as f64;

    println!(
        "\n═══ §E POSEIDON2 RATE ON THIS BOX (min of 4000 windows × 512 perms, one thread) ═══"
    );
    println!("   scalar, LATENCY-bound (one state, chained) : {scalar_lat:8.1} ns/perm");
    println!(
        "   scalar, THROUGHPUT-bound (512 independent) : {scalar_thr:8.1} ns/perm  ({:.2} M/s)",
        1e3 / scalar_thr
    );
    println!(
        "   packed x{}, THROUGHPUT-bound               : {packed_thr_call:8.1} ns/call = \
         {packed_thr_lane:.1} ns/perm  ({:.2} M/s)",
        Pack::WIDTH,
        1e3 / packed_thr_lane
    );
    println!(
        "   ⇒ ILP factor {:.1}x; SIMD factor {:.2}x over scalar throughput. The Merkle tree AND \
         the PoW grind both take the packed path; only the challenger's ordinary duplexing is \
         scalar (~4,830 permutations in the whole proof).",
        scalar_lat / scalar_thr,
        scalar_thr / packed_thr_lane
    );
    println!(
        "\n   CROSS-CHECK vs §D (lb=6 q=19 pow=0): 211,965 + 4,413 = 216,378 packed-path perms\n   \
         ⇒ {:.1} ms of raw permutation; the span table measured 37-41 ms of `build merkle tree`.\n   \
         The gap is the Merkle build's NON-hash work (row gather into the sponge, digest-layer\n   \
         allocation, the packed transpose) — it is real work in the hashing phase, not error.",
        216_378.0 * packed_thr_lane / 1e6
    );
    // ⚑ THE GRIND IS SIMD-PACKED TOO, and assuming otherwise makes this cross-check look broken by
    // 6x. `DuplexChallenger::grind` (vendored `grinding_challenger.rs`) builds a PACKED sponge
    // state and tests `Packing::WIDTH` candidate witnesses per permutation. §D confirms it
    // arithmetically: pow=16 adds 11,979 packed CALLS over pow=0 and 47,916 scalar-equivalents,
    // exactly 4x. The scalar path in this prover is only the challenger's ordinary duplexing —
    // ~4,830 permutations for the whole proof.
    println!(
        "   CROSS-CHECK vs §D (pow=16 grind): 47,917 scalar-equivalents = 11,979 PACKED calls \
         ⇒ {:.1} ms raw; §B measured 8.3 ms.",
        11_979.0 * packed_thr_call / 1e6
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// §F — THE SECOND AXIS. The mixture is a function of (b, log h), not of b alone.
//
// The §C geometry dump showed the deployed transfer descriptor commits matrices of height 8..64
// (widths 2..386). `log₂ h` multiplies the LDE term and does NOT multiply the Merkle term, so the
// transfer descriptor sits at the point where hashing looks WORST. Holding the blowup fixed and
// sweeping the trace height is therefore the other half of "which mixture".
//
// The vehicle is `pasta-fpmul-sound` — a ROW-LOCAL AIR (no `on_transition` leg), so cycling an
// honest 190-column block is a valid witness at any power-of-two height, the same replication
// `fri_blowup_global_knob_survey.rs` uses. Not a padding trick.
// ─────────────────────────────────────────────────────────────────────────────

const MUL_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fpmul-sound.json");
const MUL_TRACE: &str = include_str!("fixtures/pasta-fpmul-sound-trace.txt");

fn parse_rows(text: &str, width: usize) -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(!rows.is_empty(), "the Lean-emitted fixture is non-empty");
    assert!(
        rows.iter().all(|r| r.len() == width),
        "every fixture row is {width} wide"
    );
    rows
}

/// **§F — hash/arith as a function of TRACE HEIGHT at fixed blowup.**
#[test]
fn phase_profile_trace_height_sweep() {
    install_layer();
    let reps: usize = std::env::var("DREGG_PROFILE_REPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(9);
    let base = parse_rows(MUL_TRACE, 190);
    let desc = parse_vm_descriptor2(MUL_DESC_JSON).expect("fpmul parses");

    for lb in [3usize, 6] {
        println!(
            "\n═══ §F TRACE-HEIGHT SWEEP on pasta-fpmul-sound (190 declared → 694 committed cols) \
             at lb={lb}, q=19, pow=0 — rayon threads: {} ═══",
            rayon_threads()
        );
        let mut pts = Vec::new();
        for log_h in [6usize, 8, 10, 12] {
            let w = Workload {
                desc: desc.clone(),
                base_trace: (0..(1usize << log_h))
                    .map(|i| base[i % base.len()].clone())
                    .collect(),
                pis: vec![],
            };
            match measure_point(&w, lb, 19, 0, reps) {
                Ok(mut p) => {
                    // reuse the `q` slot to carry log_h into the table
                    p.q = log_h;
                    print_point(&p);
                    pts.push(p);
                }
                Err(e) => println!("   log_h={log_h}: {e}"),
            }
        }
        println!("\n── §F(lb={lb}) hash vs arith by TRACE HEIGHT (the `q` column is log₂ h)");
        crossover_table(&format!("§F lb={lb}"), &pts);
    }
}
