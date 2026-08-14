//! # THE GRIND PHASE — what 16 bits of `query_proof_of_work_bits` buy, what they cost, and why the
//! cost is a random draw.
//!
//! `tests/ir2_phase_profile.rs` §4 named the phase: at the deployed `(lb=6, q=19, pow=16)` the
//! PoW grind is **47,917 scalar-equivalent Poseidon2 permutations, ~8.2 ms of a 69 ms prove**, it
//! depends on **neither the blowup nor the trace**, and across one security-parity ladder it drew
//! `0.04 / 8.2 / 10.1 / 31.9 / 40.0 / 40.8 ms`. That spread manufactured a false optimum.
//!
//! This file asks the four questions that finding leaves open, and each `§G*` test answers one:
//!
//! * **§G1 — the exchange rate.** `Assurance.TwoRegimeQueryBudget` (minidregg) prices the query
//!   column as `q·(−log₂(1−θ_r)) + pow` bits, so `pow` is an *additive* term and a query is worth
//!   `−log₂(1−θ_r)` bits. At `lb = 6` that is **0.9776 bits/query at UDR**, `3` at JBR, `6` at the
//!   withdrawn CBR. The deployed 16 grind bits are therefore worth **16.37 queries at UDR**. This
//!   test recomputes the exchange rate from the same formula and PINS the three deployed cells
//!   (34 / 73 / 130) against the Lean theorem `ir2_three_regimes`.
//!
//! * **§G2 — the distribution, not the mean.** `grind(bits)` returns the SMALLEST witness whose
//!   absorbed transcript samples `bits` zero bits (the dregg `find_map_first` delta), so the
//!   returned witness value **IS the exact work**: `w+1` candidates scanned, `⌈(w+1)/lanes⌉`
//!   packed permutations. That makes the cost distribution measurable with **zero timing noise**
//!   on a contended box. Reported as percentiles over N independent transcripts.
//!
//! * **§G3 — is it parallel?** `commit_pow_cost_measure.rs` asserts the grind rate is a "WHOLE
//!   MACHINE rate, not a per-core one: there is no further thread multiplier to apply". That
//!   sentence was written against upstream's `find_map_any`. The vendored crate now uses
//!   `find_map_first` (the byte-determinism delta). `find_first` must prove no *lower* witness
//!   exists, which is a different parallel problem. This test measures the actual thread scaling of
//!   the deployed `grind` and of two alternatives, at fixed `bits` and fixed transcript.
//!
//! * **§G4 — the pow-vs-queries sweep.** At a fixed soundness column, prove/verify/bytes for
//!   `pow ∈ {0, 8, 12, 16, 20}` with `q` chosen to hold the UDR column at the deployed value.
//!   The grind term is reported BOTH as the measured draw and as its expectation, because a single
//!   draw at one `pow` is not a cost.
//!
//! ⚠ **Nothing here weakens a security parameter.** Grind bits are soundness bits; §G4 holds the
//! soundness column FIXED and moves only where the bits come from.
//!
//! Run (release only; a debug timing here is a lie):
//! ```text
//! cargo test -p dregg-circuit --release --test grind_phase_measure -- --nocapture --test-threads=1
//! ```
//! §G3 and §G4 are `#[ignore]`d (minutes of grinding / real proofs); add `--ignored`.

use std::time::Instant;

use p3_baby_bear::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::{CanObserve, DuplexChallenger, GrindingChallenger};
use p3_field::integers::QuotientMap;
use p3_field::{Field, PackedValue, PrimeCharacteristicRing, PrimeField64};
use rayon::prelude::*;

type Perm16 = Poseidon2BabyBear<16>;
type Ch = DuplexChallenger<BabyBear, Perm16, 16, 8>;
type Pack = <BabyBear as Field>::Packing;

/// A challenger whose transcript is `seed` — one observed field element, so `input_buffer.len() = 1`
/// and the grind's `witness_idx` is 1, exactly as in a real prove where the buffer is partially
/// filled. Distinct seeds are distinct transcripts and therefore independent grind draws.
fn seeded_challenger(seed: u64) -> Ch {
    let mut ch: Ch = DuplexChallenger::new(default_babybear_poseidon2_16());
    // Two observes so the sponge state is not the all-zero default, and the seed is spread over
    // two limbs (BabyBear is 31 bits).
    ch.observe(BabyBear::from_u64(seed % BabyBear::ORDER_U64));
    ch.observe(BabyBear::from_u64((seed >> 31) % BabyBear::ORDER_U64));
    ch
}

// ─────────────────────────────────────────────────────────────────────────────
// §G1 — THE EXCHANGE RATE
// ─────────────────────────────────────────────────────────────────────────────

/// `−log₂(1 − θ_r)` at rate `ρ = 2^(−lb)` — the bits ONE query buys, per regime. Mirrors
/// `Assurance.TwoRegimeQueryBudget.survivalSq`: `UDR ↦ ((1+ρ)/2)²`, `JBR ↦ ρ`, `CBR ↦ ρ²`, all
/// squared, so the per-query bits are `−log₂(√survivalSq)`.
fn bits_per_query(regime: &str, lb: usize) -> f64 {
    let rho = 2f64.powi(-(lb as i32));
    let survival = match regime {
        "UDR" => (1.0 + rho) / 2.0,
        "JBR" => rho.sqrt(),
        "CBR" => rho,
        _ => unreachable!(),
    };
    -survival.log2()
}

fn column_bits(regime: &str, lb: usize, q: usize, pow: usize) -> f64 {
    q as f64 * bits_per_query(regime, lb) + pow as f64
}

/// The smallest `q` whose column at `regime`, `lb`, `pow` reaches `target` bits.
fn queries_for(regime: &str, lb: usize, pow: usize, target: f64) -> usize {
    let per = bits_per_query(regime, lb);
    let need = (target - pow as f64).max(0.0);
    (need / per).ceil() as usize
}

#[test]
fn g1_exchange_rate_and_the_lean_cells() {
    println!("\n═══ §G1  WHAT A GRIND BIT IS WORTH, IN QUERIES ═══\n");
    println!(
        "  formula: column_bits = q · (−log₂(1−θ_r)) + pow     [Assurance.TwoRegimeQueryBudget]\n\
         \x20 `pow` is an ADDITIVE term at EVERY regime: one grind bit = one soundness bit, flat.\n\
         \x20 A QUERY is worth −log₂(1−θ_r) bits, and THAT is what moves with the regime.\n"
    );

    println!(
        "  {:<8}{:>10}{:>18}{:>26}",
        "regime", "lb", "bits per query", "queries per grind bit"
    );
    println!("  {}", "-".repeat(62));
    for regime in ["UDR", "JBR", "CBR"] {
        for lb in [3usize, 6] {
            let per = bits_per_query(regime, lb);
            println!("  {:<8}{:>10}{:>18.4}{:>26.4}", regime, lb, per, 1.0 / per);
        }
    }

    // ⚑ PIN against the Lean theorem `ir2_three_regimes : (queryErr .UDR ir2).Bits 34 ∧ … 73 ∧ … 130`.
    // `Bits k` is two-sided (`e ≤ 2^-k ∧ 2^-(k+1) < e`), so `k = ⌊column_bits⌋`.
    println!("\n  deployed IR-v2 (lb=6, q=19, pow=16), cross-checked against Lean:");
    for (regime, lean) in [("UDR", 34usize), ("JBR", 73), ("CBR", 130)] {
        let c = column_bits(regime, 6, 19, 16);
        println!(
            "    {regime}: {c:.4} bits  → floor {}  (Lean `ir2_three_regimes` says {lean})",
            c.floor() as usize
        );
        assert_eq!(
            c.floor() as usize,
            lean,
            "{regime} column disagrees with the Lean cell"
        );
    }

    println!("\n  ⚑ THE TRADE, at the deployed point:");
    for regime in ["UDR", "JBR", "CBR"] {
        let per = bits_per_query(regime, 6);
        let q_equiv = 16.0 / per;
        let pow_share = 16.0 / column_bits(regime, 6, 19, 16) * 100.0;
        println!(
            "    {regime}: the 16 grind bits are {:.1}% of the column and would cost \
             {q_equiv:.2} MORE QUERIES to buy ({} → {} queries at pow=0)",
            pow_share,
            19,
            queries_for(regime, 6, 0, column_bits(regime, 6, 19, 16))
        );
    }

    println!("\n  the UDR-parity sweep §G4 measures (target = the deployed UDR column):");
    let target = column_bits("UDR", 6, 19, 16);
    println!("    target = {target:.4} bits at UDR, lb = 6");
    println!(
        "  {:<8}{:>8}{:>14}{:>14}{:>14}",
        "pow", "q", "UDR bits", "JBR bits", "CBR bits"
    );
    println!("  {}", "-".repeat(58));
    for pow in [0usize, 8, 12, 16, 20] {
        let q = queries_for("UDR", 6, pow, target);
        println!(
            "  {:<8}{:>8}{:>14.3}{:>14.3}{:>14.3}",
            pow,
            q,
            column_bits("UDR", 6, q, pow),
            column_bits("JBR", 6, q, pow),
            column_bits("CBR", 6, q, pow),
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// §G2 — THE DISTRIBUTION OF THE GRIND'S WORK, EXACTLY (no timer involved)
// ─────────────────────────────────────────────────────────────────────────────

/// Exact work of one grind, in CANDIDATES. The dregg `find_map_first` delta makes `grind` return
/// the *globally minimal* valid witness `w`, so candidates `0..=w` were all evaluated: the returned
/// field element IS the trial count. (Under upstream's `find_map_any` this identity does not hold,
/// which is a second, unadvertised consequence of the determinism delta.)
fn grind_trials(seed: u64, bits: usize) -> u64 {
    let mut ch = seeded_challenger(seed);
    let w = ch.grind(bits);
    w.as_canonical_u64() + 1
}

fn percentile(sorted: &[f64], p: f64) -> f64 {
    if sorted.is_empty() {
        return f64::NAN;
    }
    let idx = ((sorted.len() - 1) as f64 * p).round() as usize;
    sorted[idx]
}

#[test]
fn g2_grind_work_distribution() {
    println!("\n═══ §G2  THE GRIND'S WORK IS A GEOMETRIC DRAW — the distribution, exactly ═══\n");
    println!(
        "  `grind` returns the MINIMAL valid witness, so the returned field element is the exact\n\
         \x20 trial count. No timer is involved and box contention cannot touch these numbers.\n\
         \x20 lanes = {} (SIMD width) ⇒ packed permutations = ⌈trials / lanes⌉.\n",
        Pack::WIDTH
    );

    let samples: usize = std::env::var("DREGG_GRIND_SAMPLES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(256);

    for bits in [12usize, 16] {
        let n = if bits <= 12 { samples * 4 } else { samples };
        let mut trials: Vec<f64> = (0..n as u64)
            .map(|s| grind_trials(s.wrapping_mul(0x9E37_79B9_7F4A_7C15), bits) as f64)
            .collect();
        let mean = trials.iter().sum::<f64>() / n as f64;
        trials.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let expected = 2f64.powi(bits as i32);
        println!("  bits = {bits}, N = {n} independent transcripts");
        println!(
            "    mean trials = {mean:.0}   (theory 2^{bits} = {expected:.0}; ratio {:.3})",
            mean / expected
        );
        println!(
            "    {:<12}{:>14}{:>16}{:>16}",
            "quantile", "trials", "× the mean", "packed perms"
        );
        println!("    {}", "-".repeat(58));
        for (label, p) in [
            ("min", 0.0),
            ("p10", 0.10),
            ("p50", 0.50),
            ("p90", 0.90),
            ("p99", 0.99),
            ("max", 1.0),
        ] {
            let v = percentile(&trials, p);
            println!(
                "    {:<12}{:>14.0}{:>16.2}{:>16.0}",
                label,
                v,
                v / expected,
                (v / Pack::WIDTH as f64).ceil()
            );
        }
        // The geometric/exponential model: P(trials > k·2^bits) = e^{−k}. Report the observed
        // tail masses against it so the model is CHECKED, not assumed.
        println!(
            "    {:<12}{:>14}{:>16}",
            "tail", "observed", "e^-k (theory)"
        );
        for k in [1.0f64, 2.0, 3.0, 4.0] {
            let obs = trials.iter().filter(|&&t| t > k * expected).count() as f64 / n as f64;
            println!(
                "    {:<12}{:>14.4}{:>16.4}",
                format!("P(>{k:.0}x)"),
                obs,
                (-k).exp()
            );
        }
        println!(
            "    ⇒ p99/p50 spread = {:.1}×,  max/min over N = {:.0}×\n",
            percentile(&trials, 0.99) / percentile(&trials, 0.50),
            percentile(&trials, 1.0) / percentile(&trials, 0.0).max(1.0)
        );
    }

    println!(
        "  ⚑ READ THIS AS A LATENCY BUDGET. The grind is a per-PROOF draw, not a per-run one:\n\
         \x20 for a FIXED transcript the witness is fixed (that is what the `find_map_first` delta\n\
         \x20 buys), so re-running one proof reproduces its own draw exactly. Every NEW proof draws\n\
         \x20 again. A p99 latency budget must carry the p99 of this table, not its mean."
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// §G3 — THREAD SCALING: does `find_map_first` actually parallelise?
// ─────────────────────────────────────────────────────────────────────────────

/// ⚑ **The contention-free instrument.** This box runs at load 45–95 with ~39 other sessions, so a
/// wall-clock speedup measured here is a lower bound contaminated by everyone else's work. The
/// scaling question — *does this combinator divide the search across threads?* — does not need a
/// clock: every batch is one Poseidon2 permutation, so the **critical path is the maximum number of
/// batches any single worker scanned**, and `batches(T=1) / max_per_thread(T)` is the speedup the
/// strategy would achieve on an idle machine. Counters are cache-line padded per thread.
#[repr(align(128))]
struct PaddedCounter(std::sync::atomic::AtomicU64);
static BATCHES: [PaddedCounter; 64] =
    [const { PaddedCounter(std::sync::atomic::AtomicU64::new(0)) }; 64];

fn bump_batch() {
    let i = rayon::current_thread_index().unwrap_or(63).min(63);
    BATCHES[i]
        .0
        .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

fn reset_batches() {
    for c in BATCHES.iter() {
        c.0.store(0, std::sync::atomic::Ordering::Relaxed);
    }
}

/// `(total batches scanned, max batches on any one worker)`.
fn read_batches() -> (u64, u64) {
    let v: Vec<u64> = BATCHES
        .iter()
        .map(|c| c.0.load(std::sync::atomic::Ordering::Relaxed))
        .collect();
    (v.iter().sum(), v.iter().copied().max().unwrap_or(0))
}

/// The deployed inner loop, lifted verbatim out of `grinding_challenger.rs` so the three search
/// STRATEGIES below differ in nothing but the rayon combinator. Returns the minimal matching
/// candidate inside batch `batch`, or `None`.
#[inline]
fn scan_batch(
    perm: &Perm16,
    base_packed_state: &[Pack; 16],
    witness_idx: usize,
    batch: u64,
    mask: u64,
) -> Option<BabyBear> {
    use p3_symmetric::Permutation;
    bump_batch();
    const RATE: usize = 8;
    let lanes = Pack::WIDTH as u64;
    let order = BabyBear::ORDER_U64;
    let base = batch * lanes;
    let mut packed_state = *base_packed_state;
    let packed_witnesses = Pack::from_fn(|lane| {
        let candidate = base + lane as u64;
        if candidate < order {
            unsafe { BabyBear::from_canonical_unchecked(candidate) }
        } else {
            BabyBear::NEG_ONE
        }
    });
    packed_state[witness_idx] = packed_witnesses;
    perm.permute_mut(&mut packed_state);
    packed_state[RATE - 1]
        .as_slice()
        .iter()
        .zip(packed_witnesses.as_slice())
        .find(|(sample, _)| (sample.as_canonical_u64() & mask) == 0)
        .map(|(_, &w)| w)
}

fn base_state(ch: &Ch) -> ([Pack; 16], usize) {
    let st: [Pack; 16] = core::array::from_fn(|i| {
        if i < ch.input_buffer.len() {
            Pack::from(ch.input_buffer[i])
        } else {
            Pack::from(ch.sponge_state[i])
        }
    });
    (st, ch.input_buffer.len())
}

/// **Strategy A — THE PRE-2026-08-14 DEPLOYED SEARCH.**
/// `(0..num_batches).into_par_iter().find_map_first(..)`, i.e. `DuplexChallenger::grind`'s body as
/// it stood between `90680ee7d` (the determinism delta) and the schedule fix.
///
/// ⚑ **This is now the DIFFERENTIAL ORACLE, not a copy of the deployed code.** §G6 asserts, over 64
/// independent transcripts, that today's `grind` returns exactly what this returns — old path
/// against new path, same seed, same witness. Do not delete it and do not "simplify" it into a call
/// to `grind`; it earns its place precisely by being the code that is no longer there.
fn grind_first(ch: &Ch, bits: usize) -> BabyBear {
    let (st, widx) = base_state(ch);
    let mask = (1u64 << bits) - 1;
    let num_batches = BabyBear::ORDER_U64.div_ceil(Pack::WIDTH as u64);
    let perm = ch.permutation.clone();
    (0..num_batches)
        .into_par_iter()
        .find_map_first(|b| scan_batch(&perm, &st, widx, b, mask))
        .expect("witness")
}

/// **Strategy B — UPSTREAM.** `find_map_any`: whichever worker finds a match first wins. Fully
/// parallel, but the witness depends on thread scheduling — this is the shape the dregg delta
/// replaced, and the byte-parity gates are why.
fn grind_any(ch: &Ch, bits: usize) -> BabyBear {
    let (st, widx) = base_state(ch);
    let mask = (1u64 << bits) - 1;
    let num_batches = BabyBear::ORDER_U64.div_ceil(Pack::WIDTH as u64);
    let perm = ch.permutation.clone();
    (0..num_batches)
        .into_par_iter()
        .find_map_any(|b| scan_batch(&perm, &st, widx, b, mask))
        .expect("witness")
}

/// **Strategy C — LANDED 2026-08-14: WINDOWED PARALLEL MIN.** Scan a bounded window of `window` batches
/// **completely** and in parallel, and reduce with `min`. If the window holds a match, its minimum
/// IS the global minimum, so this returns **byte-for-byte the same witness as Strategy A** — same
/// predicate, same soundness, same proof bytes; only the schedule changes. If it holds none,
/// advance to the next window (probability `e^(−window·lanes/2^bits)` per window).
///
/// The point: every window is a FULL parallel scan with no early exit, so it saturates `T` threads,
/// and the work is bounded by a whole number of windows instead of by a geometric draw.
/// ⚑ **The SCHEDULE here is the LANDED one, not a copy of it.** The loop, the window advance and
/// the min-reduction are `p3_challenger::windowed_find_map_first` — the exact function
/// `DuplexChallenger::grind` now calls. All this wrapper adds is the per-thread batch counter,
/// which cannot live in the vendored crate, and which is the whole reason a copy of `scan_batch`
/// exists at all. So the AFTER column below counts operations performed by shipped code.
fn grind_windowed(ch: &Ch, bits: usize, window: u64) -> (BabyBear, u64) {
    let (st, widx) = base_state(ch);
    let mask = (1u64 << bits) - 1;
    let num_batches = BabyBear::ORDER_U64.div_ceil(Pack::WIDTH as u64);
    let perm = ch.permutation.clone();
    let w = p3_challenger::windowed_find_map_first(num_batches, window, |b| {
        scan_batch(&perm, &st, widx, b, mask)
    })
    .expect("witness");
    // Windows consumed, exactly, from the witness itself: the answer sits in batch `w / lanes`,
    // and windows are contiguous from 0.
    let windows = w.as_canonical_u64() / (Pack::WIDTH as u64 * window) + 1;
    (w, windows)
}

/// Batches on the critical path and in total for the WINDOWED schedule, **derived** rather than
/// timed: given the minimal witness `w`, the answer is in batch `w / lanes`, so the schedule
/// consumes `n = w/(lanes·window) + 1` whole windows; each is scanned completely and splits across
/// `t` workers. Exact, and it reproduces on any machine. §G3 checks it against the counters.
fn windowed_counts(witness: u64, window: u64, t: u64) -> (u64, u64) {
    let n = witness / (Pack::WIDTH as u64 * window) + 1;
    let total = n * window;
    let crit = n * window.div_ceil(t);
    (crit, total)
}

fn pool(n: usize) -> rayon::ThreadPool {
    rayon::ThreadPoolBuilder::new()
        .num_threads(n)
        .build()
        .expect("pool")
}

#[test]
#[ignore = "MEASUREMENT: many full grinds across thread counts. --ignored --nocapture"]
fn g3_grind_thread_scaling() {
    let bits: usize = std::env::var("DREGG_GRIND_BITS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(16);
    let reps: usize = std::env::var("DREGG_GRIND_REPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(7);
    let max_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8);

    println!("\n═══ §G3  DOES THE DEPLOYED GRIND PARALLELISE? ═══\n");
    println!(
        "  bits = {bits}, min of {reps}, SIMD lanes = {}, box parallelism = {max_threads}",
        Pack::WIDTH
    );
    println!(
        "  A = `find_map_first`, the schedule DEPLOYED 2026-08-02..2026-08-14 (the BEFORE column)\n\
         \x20 B = `find_map_any`, upstream Plonky3 — fast and byte-NONDETERMINISTIC, kept as the\n\
         \x20     reason A exists at all\n\
         \x20 C = windowed parallel min, LANDED 2026-08-14 (the AFTER column)\n\
         \x20 D = the real `DuplexChallenger::grind` as it now stands, measured through the vendored\n\
         \x20     crate so the AFTER number is the LANDED code and not C's copy of it"
    );

    // ONE fixed transcript, so all three strategies and all thread counts face the SAME draw and
    // the comparison is not a lottery. Seed chosen for a near-median draw (see §G2).
    let mut seed = 0u64;
    let mut trials = 0u64;
    for s in 0..4096u64 {
        let t = grind_trials(s.wrapping_mul(0x9E37_79B9_7F4A_7C15), bits);
        let target = 1u64 << bits;
        if t > target && t < 2 * target {
            seed = s.wrapping_mul(0x9E37_79B9_7F4A_7C15);
            trials = t;
            break;
        }
    }
    let ch = seeded_challenger(seed);
    let w_ref = grind_first(&ch, bits);
    // ⚑ PIN THE REIMPLEMENTATION TO THE DEPLOYED ONE. Strategy A is a copy of
    // `DuplexChallenger::grind`'s body lifted out so the three strategies differ only in the rayon
    // combinator. If the copy has drifted, every number below measures a paraphrase instead of the
    // deployed grind, and nothing else in this test would notice.
    assert_eq!(
        w_ref,
        seeded_challenger(seed).grind(bits),
        "strategy A must reproduce the DEPLOYED `DuplexChallenger::grind` witness exactly"
    );
    println!(
        "  fixed transcript: minimal witness = {}, trials = {trials} ({:.2}× the mean), \
         packed perms = {}\n",
        w_ref.as_canonical_u64(),
        trials as f64 / 2f64.powi(bits as i32),
        trials.div_ceil(Pack::WIDTH as u64)
    );

    fn time_it<F: Fn() -> BabyBear + Send + Sync>(t: usize, reps: usize, f: F) -> f64 {
        let p = pool(t);
        let mut best = f64::INFINITY;
        for _ in 0..reps {
            let t0 = Instant::now();
            let w = p.install(&f);
            let dt = t0.elapsed().as_secs_f64() * 1000.0;
            std::hint::black_box(w);
            best = best.min(dt);
        }
        best
    }

    let mut threads: Vec<usize> = vec![1, 2, 4, 8];
    if max_threads > 8 {
        threads.push(max_threads);
    }
    threads.retain(|&t| t <= max_threads.max(1));
    threads.dedup();

    // The window the LANDED grind uses: `c = 1/4`, i.e. `2^bits / 4` candidates a window.
    let window = p3_challenger::default_grind_window(bits, Pack::WIDTH as u64);

    /// One (strategy, threads) cell: wall clock AND the contention-free critical path.
    fn cell<F: Fn() -> BabyBear + Send + Sync>(t: usize, reps: usize, f: F) -> (f64, u64, u64) {
        let ms = time_it(t, reps, &f);
        let p = pool(t);
        reset_batches();
        std::hint::black_box(p.install(&f));
        let (total, max) = read_batches();
        (ms, total, max)
    }

    // ═════════════════════════════════════════════════════════════════════════════════════════
    // ⚑ THE HEADLINE IS AN OPERATION COUNT, NOT A CLOCK. This box is an M2 Max at load average
    // 16–95 with ~36 login sessions; a wall-clock speedup measured here is an artefact with a
    // trend in it. Every batch is exactly one packed Poseidon2 permutation, so:
    //
    //   `crit`  = max batches scanned by any ONE worker = the CRITICAL PATH. This is what the
    //             fix reduces, and it is a LATENCY claim.
    //   `total` = batches scanned by all workers together = the WORK. The fix makes this go UP,
    //             because a whole window is scanned instead of stopping at the first hit.
    //
    // ⚠ These two never multiply into one number. A critical-path ratio is not a throughput
    // ratio and composing them mixes units.
    // ═════════════════════════════════════════════════════════════════════════════════════════
    println!(
        "  ── ① EXACT OPERATION COUNTS (batches = packed Poseidon2 permutations, no clock) ──\n\
         \x20 `crit` = the CRITICAL PATH (max batches on any one worker); `scale` = crit(1)/crit(T).\n\
         \x20 `total` = the WORK (all workers). The fix trades total UP for crit DOWN.\n"
    );
    println!(
        "  {:<8}| {:>9}{:>7}{:>10} | {:>9}{:>7}{:>10} | {:>9}{:>7}{:>10}",
        "threads",
        "A crit",
        "scale",
        "A total",
        "B crit",
        "scale",
        "B total",
        "C crit",
        "scale",
        "C total"
    );
    println!("  {}", "-".repeat(96));
    let mut base_crit = (1u64, 1u64, 1u64);
    let mut rows = Vec::new();
    for (i, &t) in threads.iter().enumerate() {
        let (a, at, ac) = cell(t, reps, || grind_first(&ch, bits));
        let (b, bt, bc) = cell(t, reps, || grind_any(&ch, bits));
        let (c, ct, cc) = cell(t, reps, || grind_windowed(&ch, bits, window).0);
        // D: the LANDED `DuplexChallenger::grind` end to end. Wall clock only — the batch counter
        // lives in this file's `scan_batch`, not in the vendored crate — and reported as a clock,
        // i.e. as the weakest column here.
        let d = time_it(t, reps, || ch.clone().grind(bits));
        if i == 0 {
            base_crit = (ac.max(1), bc.max(1), cc.max(1));
        }
        println!(
            "  {:<8}| {:>9}{:>7.2}{:>10} | {:>9}{:>7.2}{:>10} | {:>9}{:>7.2}{:>10}",
            t,
            ac,
            base_crit.0 as f64 / ac.max(1) as f64,
            at,
            bc,
            base_crit.1 as f64 / bc.max(1) as f64,
            bt,
            cc,
            base_crit.2 as f64 / cc.max(1) as f64,
            ct,
        );
        rows.push((t, a, b, c, d, ac, cc, at, ct));
    }

    // ⚑ Cross-check the counters against the DERIVED counts. If rayon's splitter is doing what
    // the derivation says, these agree; if they disagree, the derivation in `grind-fix.md` is
    // wrong and the counter is right. Reported, not asserted, because rayon may split unevenly.
    println!("\n  ── ② the AFTER column, derived vs counted (a check on the model) ──");
    println!(
        "  {:<10}{:>14}{:>14}{:>14}{:>14}",
        "threads", "crit derived", "crit counted", "total derived", "total counted"
    );
    for (t, _, _, _, _, _, cc, _, ct) in &rows {
        let (dc, dt) = windowed_counts(w_ref.as_canonical_u64(), window, *t as u64);
        println!("  {:<10}{:>14}{:>14}{:>14}{:>14}", t, dc, cc, dt, ct);
    }

    // ⚑ THE WORK BASELINE IS `A` AT ONE THREAD, AND SAYING SO IS THE POINT. `A`'s total work
    // RISES with T (eleven workers scanning candidates above the answer and losing the min), so
    // dividing C's work by A's work AT THE SAME T flatters the fix — it would report the schedule
    // change as a work REDUCTION. The honest denominator for a work ratio is the least work the
    // old path ever did, which is its single-threaded run; both ratios are printed so neither can
    // be quoted alone.
    let (work_base, crit_base) = (rows[0].7, rows[0].5);
    println!(
        "\n  ⚑ ③ BEFORE vs AFTER, the result that survives a busy box (one fixed transcript):\n\
         \x20 `crit ×` = the LATENCY win, against A's critical path at the same T.\n\
         \x20 `work × (vs A@1)` = the PRICE, against the least work the old path ever did.\n\
         \x20 `work × (vs A@T)` = the same work against the old path AS DEPLOYED at that T.\n\
         \x20 ⚠ These are different units. Never multiply a crit ratio by a work ratio."
    );
    println!(
        "  {:<9}{:>12}{:>12}{:>9}{:>14}{:>14}{:>14}{:>14}",
        "threads",
        "crit BEFORE",
        "crit AFTER",
        "crit ×",
        "work BEFORE",
        "work AFTER",
        "work × A@1",
        "work × A@T"
    );
    for (t, _, _, _, _, ac, cc, at, ct) in &rows {
        println!(
            "  {:<9}{:>12}{:>12}{:>9.2}{:>14}{:>14}{:>14.2}{:>14.2}",
            t,
            ac,
            cc,
            *ac as f64 / (*cc).max(1) as f64,
            at,
            ct,
            *ct as f64 / work_base.max(1) as f64,
            *ct as f64 / (*at).max(1) as f64,
        );
    }
    println!(
        "  ⇒ against the old path's own best case (A at 1 thread: {crit_base} batches critical, \
         {work_base} total),\n\
         \x20 the landed schedule is {:.2}× on the critical path at {} threads and costs {:.2}× the work.",
        crit_base as f64 / (rows.last().unwrap().6).max(1) as f64,
        rows.last().unwrap().0,
        rows.last().unwrap().8 as f64 / work_base.max(1) as f64,
    );

    println!(
        "\n  ── ④ wall clock, min of {reps} ──  ⚠ NOT EVIDENCE ON THIS BOX (load average {}); an\n\
         \x20 upper bound with a contention trend in it. The counts above are the result.",
        std::fs::read_to_string("/proc/loadavg")
            .ok()
            .and_then(|s| s.split_whitespace().next().map(str::to_string))
            .unwrap_or_else(|| "see the run header".into())
    );
    println!(
        "  {:<10}{:>12}{:>12}{:>12}{:>16}",
        "threads", "A ms", "B ms", "C ms", "D ms (LANDED)"
    );
    for (t, a, b, c, d, ..) in &rows {
        println!("  {:<10}{:>12.2}{:>12.2}{:>12.2}{:>16.2}", t, a, b, c, d);
    }

    // The correctness claim that makes strategy C a SCHEDULING change and not a protocol change.
    let (w_win, nwin) = grind_windowed(&ch, bits, window);
    assert_eq!(
        w_win, w_ref,
        "windowed-min must return the SAME witness as find_map_first"
    );
    println!(
        "\n  ⚑ strategy C returned the SAME witness ({}) in {nwin} window(s) — the proof bytes are\n\
         \x20 unchanged, the predicate is unchanged, only the schedule is.",
        w_win.as_canonical_u64()
    );

    // Strategy B's witness is NOT stable — the reason the delta exists. Show it rather than assert
    // it (on 1 thread `find_any` degenerates to `find_first`).
    if max_threads > 1 {
        let p = pool(max_threads);
        let mut seen: Vec<u64> = (0..8)
            .map(|_| p.install(|| grind_any(&ch, bits)).as_canonical_u64())
            .collect();
        seen.sort_unstable();
        seen.dedup();
        println!(
            "  strategy B over 8 runs on {max_threads} threads returned {} distinct witness(es) \
             {seen:?} — the byte-determinism this tree needs is exactly what it costs.",
            seen.len()
        );
    }

    // ── CHOOSING THE WINDOW, from the measured distribution rather than from roundness ────────
    //
    // The window constant `c` (a window covers `c·2^bits` candidates) is swept through the REAL
    // `grind_with_window`, so this table prices the landed code at every candidate setting.
    //
    // ⚑ The window COUNT needs no separate harness and no clock: `grind` returns the minimal
    // witness `w`, so the number of windows a schedule with window `win` would consume is exactly
    // `w / (win·lanes) + 1`. That is an exact function of the SAME draw at every `c`, which is why
    // the distribution column below is comparable across rows and immune to this box.
    println!(
        "\n  ── ⑤ CHOOSING THE WINDOW, in operation counts over {n_draws} independent draws ──\n\
         \x20 All columns are exact batch counts at T = {max_threads}, in units of the BEFORE path's\n\
         \x20 own mean critical path (= its mean draw, since it has no parallelism). So `crit` < 1\n\
         \x20 is the latency win and `work` > 1 is what it costs.",
        n_draws = 512,
    );
    // ⚑ THE TWO CONSTANTS THAT TURN COUNTS INTO A LATENCY, MEASURED IN ISOLATION.
    //
    // Every exact column in this table says "smaller `c` is better", monotonically and without
    // limit — fewer batches on the critical path AND less total work. The only thing that stops
    // `c → 0` is the per-window rayon join, and a join is invisible to an operation count. Timing
    // a whole grind to see it does not work on this box: across two runs at load 24 and load 62
    // the `ms @max` column below moved its own minimum from `c = 1/4` to `c = 2`, which is noise
    // choosing the parameter.
    //
    // So the two constants are measured on their own, where a min-of-N is meaningful because the
    // operation is microseconds and repeated thousands of times, and the LATENCY is then DERIVED
    // from the exact counts. That is a model with two measured inputs, not a benchmark.
    let perm_ns = sweep::packed_rate_ns();
    let join_ns = {
        // One window's worth of rayon dispatch + reduce with no work in it: the same task count a
        // real window is split into (`threads * GRIND_TASKS_PER_WORKER`), every task returning
        // `None`. That is exactly the barrier the window pays.
        let p = pool(max_threads);
        let tasks = max_threads * 8;
        let mut best = f64::INFINITY;
        for _ in 0..4096 {
            let t0 = Instant::now();
            let r = p.install(|| {
                (0..tasks)
                    .into_par_iter()
                    .with_max_len(1)
                    .filter_map(|k| {
                        if k == usize::MAX {
                            Some((k, 0u8))
                        } else {
                            None
                        }
                    })
                    .min_by_key(|&(k, _)| k)
            });
            std::hint::black_box(r);
            best = best.min(t0.elapsed().as_secs_f64() * 1e9);
        }
        best
    };
    println!(
        "  measured constants: packed Poseidon2 {perm_ns:.0} ns/batch, one window barrier \
         {:.1} µs ({} tasks on {max_threads} threads, min of 4096)",
        join_ns / 1000.0,
        max_threads * 8
    );
    println!(
        "  {:<8}{:>10}{:>12}{:>12}{:>12}{:>12}{:>12}{:>10}{:>10}{:>11}{:>11}{:>24}",
        "c",
        "batches",
        "crit mean",
        "crit p99",
        "crit max",
        "work mean",
        "work p99",
        "E[wins]",
        "barrier%",
        "est ms",
        "ms @max*",
        "windows over 512 draws"
    );
    println!("  {}", "-".repeat(145));
    // 512 independent draws. `grind` returns the minimal witness, so each draw fixes the batch the
    // answer sits in, and every `c` below is evaluated against the SAME 512 draws — the comparison
    // is not a lottery and nothing here involves a timer.
    let draws: Vec<u64> = (0..512u64)
        .map(|s| {
            seeded_challenger(s.wrapping_mul(0x1234_5678_9ABC_DEF1))
                .grind(bits)
                .as_canonical_u64()
        })
        .collect();
    // The BEFORE path's critical path on a draw is `w/lanes + 1` batches, walked by one worker at
    // EVERY thread count (measured scale 1.00). That is the denominator for the whole table.
    let before_crit: Vec<f64> = draws
        .iter()
        .map(|w| (w / Pack::WIDTH as u64 + 1) as f64)
        .collect();
    let before_mean = before_crit.iter().sum::<f64>() / before_crit.len() as f64;
    let mut before_sorted = before_crit.clone();
    before_sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
    // The BEFORE row, in the same normalised units, so the AFTER rows are read against the thing
    // they replace and not against an unstated baseline. Its crit and its work are the SAME
    // number at T=1 and its crit does not move with T at all (scale 1.00, table ①).
    println!(
        "  {:<8}{:>10}{:>12.3}{:>12.3}{:>12.3}{:>12.3}{:>12.3}{:>10}{:>10}{:>11.2}{:>11}",
        "BEFORE",
        "-",
        1.000,
        percentile(&before_sorted, 0.99) / before_mean,
        percentile(&before_sorted, 1.0) / before_mean,
        1.000,
        percentile(&before_sorted, 0.99) / before_mean,
        "-",
        "-",
        before_mean * perm_ns / 1e6,
        "-",
    );
    println!(
        "  (BEFORE, `find_map_first`: mean critical path {before_mean:.0} batches at EVERY thread \
         count — the 1.00 denominator.\n\
         \x20 Its p99 and max are the geometric tail of the draw itself: that tail is what the\n\
         \x20 window replaces with a tail in whole windows.)"
    );
    for (num, den) in [
        (1u64, 16u64),
        (1, 8),
        (1, 4),
        (1, 2),
        (1, 1),
        (2, 1),
        (4, 1),
        (8, 1),
    ] {
        let win = ((num << bits) / (den * Pack::WIDTH as u64)).max(1);
        let mut crit: Vec<f64> = Vec::with_capacity(draws.len());
        let mut work: Vec<f64> = Vec::with_capacity(draws.len());
        let mut wins = std::collections::BTreeMap::new();
        for w in &draws {
            let (cr, wk) = windowed_counts(*w, win, max_threads as u64);
            crit.push(cr as f64);
            work.push(wk as f64);
            *wins
                .entry(w / (win * Pack::WIDTH as u64) + 1)
                .or_insert(0usize) += 1;
        }
        let crit_mean = crit.iter().sum::<f64>() / crit.len() as f64;
        let work_mean = work.iter().sum::<f64>() / work.len() as f64;
        let mean_windows =
            wins.iter().map(|(n, k)| *n as f64 * *k as f64).sum::<f64>() / draws.len() as f64;
        crit.sort_by(|a, b| a.partial_cmp(b).unwrap());
        work.sort_by(|a, b| a.partial_cmp(b).unwrap());
        // ⚑ THE ONE COLUMN HERE THAT NEEDS A CLOCK, AND WHY. Every other column says smaller `c`
        // is better without limit — fewer batches on the critical path AND less total work. The
        // thing that stops `c → 0` is the per-window rayon join, and a join is not an operation
        // count: it is invisible to every exact column in this table. So it has to be timed. Read
        // it as a contended upper bound whose SHAPE (where it stops improving) is the signal, not
        // its absolute value.
        let ms = time_it(max_threads, reps, || {
            ch.clone().grind_with_window(bits, win)
        });
        // DERIVED latency: exact counts × the two measured constants. One window costs its own
        // batches split across the pool, plus one barrier.
        let window_ns = (win as f64 / max_threads as f64) * perm_ns;
        let est_ms = mean_windows * (window_ns + join_ns) / 1e6;
        println!(
            "  {:<8}{:>10}{:>12.3}{:>12.3}{:>12.3}{:>12.3}{:>12.3}{:>10.2}{:>9.1}%{:>11.2}{:>11.2}{:>24}",
            format!("{num}/{den}"),
            win,
            crit_mean / before_mean,
            percentile(&crit, 0.99) / before_mean,
            percentile(&crit, 1.0) / before_mean,
            work_mean / before_mean,
            percentile(&work, 0.99) / before_mean,
            mean_windows,
            100.0 * join_ns / (window_ns + join_ns),
            est_ms,
            ms,
            format!("{wins:?}")
        );
    }
    println!(
        "  * `est ms` is DERIVED (exact counts × the two measured constants) and is the column to\n\
         \x20 read. `ms @max` is a raw contended min-of-{reps} on this box and is printed only so\n\
         \x20 the disagreement is visible: at load 24 its minimum sat at c = 1/4, at load 62 it\n\
         \x20 moved to c = 2. A number that reorders under someone else's build is not a choice."
    );
    println!(
        "  ⚑ READ THE TWO HALVES SEPARATELY AND NEVER MULTIPLY THEM. `crit` is a LATENCY ratio and\n\
         \x20 `work` is a THROUGHPUT ratio; they move in opposite directions and have different\n\
         \x20 units. The fix buys critical path and PAYS in total work, and the `work mean` column\n\
         \x20 is that price, measured, at every candidate window."
    );
    println!(
        "  (⇒ latency is QUANTISED in whole windows with a geometric TAIL IN WINDOW COUNT, not in\n\
         \x20 candidates: `P(> n windows) = e^(−c·n)`, so the p99 is a small integer multiple of a\n\
         \x20 fixed, parallel, predictable unit rather than 4.6× the mean.)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// §G6 — THE CORRECTNESS OBLIGATION: the landed schedule returns the OLD PATH'S WITNESS
// ─────────────────────────────────────────────────────────────────────────────

/// ⚑ **This is the test that makes the schedule fix free rather than a protocol change**, and it
/// is checked three ways because "same witness" is the whole claim:
///
/// 1. **Old path vs new path, same seed.** `grind_first` above is the pre-2026-08-14 body —
///    `find_map_first` over the whole candidate range — kept as a differential oracle. Today's
///    `DuplexChallenger::grind` is the windowed parallel min. Over `N` independent transcripts they
///    must return the *same field element*. Because everything downstream of the grind (query
///    indices, opened values, varint lengths) is a pure function of the transcript that witness is
///    absorbed into, equal witnesses ⇒ equal proofs, byte for byte.
///
/// 2. **Against the DEFINITION, not against the oracle.** An oracle can drift into agreeing with
///    the thing it checks. So for a subset we verify the *contract itself* exhaustively: every
///    candidate strictly below the returned witness FAILS `check_witness`. The minimal valid
///    witness is unique, so this pins `grind` to a specification rather than to another program.
///
/// 3. **Window invariance, including `window = 1`.** The window is a schedule parameter; if it
///    could reach the answer, this is where it would show. `window = 1` degenerates to a literal
///    sequential in-order scan — the specification in (2) executed by the deployed code — and
///    `window = 1 << 24` is one giant parallel window. Every size in between must agree.
///
/// Runs at the deployed `bits = 16` and at `bits = 14` (the `recursion-verify` default), because a
/// window is computed from `bits` and a bug in that arithmetic would be `bits`-specific.
#[test]
fn g6_windowed_grind_returns_the_old_paths_witness() {
    let n: u64 = std::env::var("DREGG_GRIND_PARITY_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(64);

    println!("\n═══ §G6  THE WINDOWED GRIND RETURNS THE OLD PATH'S WITNESS ═══\n");

    for bits in [16usize, 14] {
        // ── 1. old path vs new path, N independent transcripts ──────────────────────────────
        let mut worst = 0u64;
        for s in 0..n {
            let seed = s.wrapping_mul(0x9E37_79B9_7F4A_7C15);
            let ch = seeded_challenger(seed);
            let old = grind_first(&ch, bits);
            let new = ch.clone().grind(bits);
            assert_eq!(
                old, new,
                "bits={bits} seed={seed}: the windowed schedule returned a DIFFERENT witness \
                 than `find_map_first` — the fix is not free and the proof bytes have moved"
            );
            worst = worst.max(new.as_canonical_u64());
        }
        println!(
            "  bits = {bits}: {n} transcripts, old `find_map_first` == new windowed grind on every \
             one (largest witness seen {worst})"
        );

        // ── 2. the CONTRACT, exhaustively: nothing below the witness is valid ───────────────
        let checked = 8u64.min(n);
        let mut candidates_checked = 0u64;
        for s in 0..checked {
            let seed = s.wrapping_mul(0x9E37_79B9_7F4A_7C15);
            let ch = seeded_challenger(seed);
            let w = ch.clone().grind(bits).as_canonical_u64();
            let lower_hit = (0..w).into_par_iter().any(|c| {
                // SAFETY: `c < w < p`.
                let cand = unsafe { BabyBear::from_canonical_unchecked(c) };
                ch.clone().check_witness(bits, cand)
            });
            assert!(
                !lower_hit,
                "bits={bits} seed={seed}: a candidate below the returned witness {w} satisfies \
                 the PoW predicate — `grind` is not returning the MINIMAL witness"
            );
            candidates_checked += w;
        }
        println!(
            "    minimality verified EXHAUSTIVELY on {checked} transcripts \
             ({candidates_checked} candidates below the witness, every one invalid)"
        );

        // ── 3. window invariance ────────────────────────────────────────────────────────────
        // A window of 1 batch is a sequential in-order scan; 1 << 24 batches is one window over
        // 4x the whole expected draw. Neither may move the answer.
        let seed = 0x51ED_5EEDu64;
        let ch = seeded_challenger(seed);
        let reference = ch.clone().grind(bits);
        for window in [1u64, 3, 64, 997, 4096, 16_384, 65_536, 1 << 20, 1 << 24] {
            let got = ch.clone().grind_with_window(bits, window);
            assert_eq!(
                got, reference,
                "bits={bits}: window {window} changed the witness — the window is supposed to be \
                 unable to reach the answer"
            );
        }
        println!(
            "    window invariance: 9 window sizes from 1 batch to 2^24 all returned {} \n",
            reference.as_canonical_u64()
        );
    }

    println!(
        "  ⚑ Equal witnesses are equal PROOFS: the witness is absorbed into Fiat-Shamir BEFORE the\n\
         \x20 first query index is drawn, so everything downstream is a pure function of it.\n\
         \x20 §G7 checks that end-to-end on real serialized proofs rather than relying on this."
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// §G4 — POW vs QUERIES AT FIXED SOUNDNESS, ON REAL PROOFS
// ─────────────────────────────────────────────────────────────────────────────

mod sweep {
    use super::*;
    use dregg_circuit::descriptor_ir2::{
        MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_with_config,
        verify_vm_descriptor2_with_config,
    };
    use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace};
    use dregg_circuit::effect_vm_descriptors::descriptor2_for_key;
    use dregg_circuit::plonky3_prover::create_config_with_fri;

    /// ⚑ `dregg_circuit::field::BabyBear` is a dregg NEWTYPE (`pub struct BabyBear(pub u32)`), not
    /// `p3_baby_bear::BabyBear`. The descriptor surface speaks the former; the grind speaks the
    /// latter. Naming both is the only way this file compiles, and the distinction is real.
    use dregg_circuit::field::BabyBear as DBabyBear;

    struct Workload {
        desc: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
        base_trace: Vec<Vec<DBabyBear>>,
        pis: Vec<DBabyBear>,
    }

    /// The SAME real transfer effect `ir2_phase_profile.rs` and `effect_vm_ir2_size_measure` price.
    fn transfer_workload() -> Workload {
        let state = CellState::new(100_000, 0);
        let effects = vec![Effect::Transfer {
            amount: 50,
            direction: 1,
        }];
        let (base_trace, pis) = generate_effect_vm_trace(&state, &effects);
        let v2_json = descriptor2_for_key("transferVmDescriptor2").expect("v2 transfer descriptor");
        let desc = parse_vm_descriptor2(v2_json).expect("v2 transfer descriptor parses");
        let dpis: Vec<DBabyBear> = pis[..desc.public_input_count].to_vec();
        Workload {
            desc,
            base_trace,
            pis: dpis,
        }
    }

    struct Row {
        pow: usize,
        q: usize,
        prove_ms: f64,
        verify_ms: f64,
        bytes: usize,
    }

    fn measure(w: &Workload, lb: usize, q: usize, pow: usize, reps: usize) -> Row {
        let config = create_config_with_fri(lb, 0, 3, q, pow);
        let mem_boundary = MemBoundaryWitness::default();
        let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
        let mut best_p = f64::INFINITY;
        let mut best_v = f64::INFINITY;
        let mut bytes = 0usize;
        for _ in 0..reps {
            let t0 = Instant::now();
            let proof = prove_vm_descriptor2_with_config(
                &w.desc,
                &w.base_trace,
                &w.pis,
                &mem_boundary,
                &map_heaps,
                &config,
            )
            .expect("prove");
            let p = t0.elapsed().as_secs_f64() * 1000.0;
            let t1 = Instant::now();
            verify_vm_descriptor2_with_config(&w.desc, &proof, &w.pis, &config).expect("verify");
            let v = t1.elapsed().as_secs_f64() * 1000.0;
            best_p = best_p.min(p);
            best_v = best_v.min(v);
            bytes = rmp_serde::to_vec(&proof).map(|x| x.len()).unwrap_or(0);
        }
        Row {
            pow,
            q,
            prove_ms: best_p,
            verify_ms: best_v,
            bytes,
        }
    }

    /// Poseidon2 packed-call rate, measured here so the expected-grind column is not imported.
    pub(super) fn packed_rate_ns() -> f64 {
        use p3_symmetric::Permutation;
        let perm = default_babybear_poseidon2_16();
        let mut st: [Pack; 16] = core::array::from_fn(|i| Pack::from(BabyBear::from_u64(i as u64)));
        // warm
        for _ in 0..1024 {
            perm.permute_mut(&mut st);
        }
        let mut best = f64::INFINITY;
        for _ in 0..2000 {
            let t0 = Instant::now();
            for _ in 0..512 {
                perm.permute_mut(&mut st);
            }
            let dt = t0.elapsed().as_secs_f64() * 1e9 / 512.0;
            best = best.min(dt);
        }
        std::hint::black_box(st);
        best
    }

    /// ⚑ **§G5 — DOES THE GRIND GATE BITE?** A constructive falsifier, and the tree did not have
    /// one.
    ///
    /// `deployed_refines_verifier_teeth.rs` records that six different tampers all reject with
    /// `InvalidPowWitness` — but every one of those is a **transcript desync**: the mutation is to
    /// an opened value or a public input, the Fiat–Shamir state moves, and the honest witness stops
    /// satisfying the predicate. **None of them mutates the witness.** So "a proof carrying a
    /// witness that does not satisfy the 16-bit condition is refused" was, until this test, a
    /// reading of `verifier.rs:254` and not a measured refusal.
    ///
    /// The mutation here is **constructive, not probabilistic**, and it is the dregg determinism
    /// delta that makes it so: `find_map_first` returns the **minimal** valid witness `w`, therefore
    /// **every** candidate below `w` is known-invalid. Replacing `w` with `w − 1` is a witness that
    /// provably fails `check_witness` — no "almost certainly", no 2^−16 slack, nothing that could
    /// quietly become a no-op the way a `replacen` of an absent string did.
    #[test]
    fn g5_the_grind_gate_bites_on_a_bad_witness() {
        let w = transfer_workload();
        let config = create_config_with_fri(6, 0, 3, 19, 16);
        let mem_boundary = MemBoundaryWitness::default();
        let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
        let mut proof = prove_vm_descriptor2_with_config(
            &w.desc,
            &w.base_trace,
            &w.pis,
            &mem_boundary,
            &map_heaps,
            &config,
        )
        .expect("honest prove");

        verify_vm_descriptor2_with_config(&w.desc, &proof, &w.pis, &config)
            .expect("the honest proof verifies");

        let honest = proof.opening_proof.query_pow_witness;
        let hv = honest.as_canonical_u64();
        println!("\n═══ §G5  THE GRIND GATE, FALSIFIED CONSTRUCTIVELY ═══\n");
        println!("  honest minimal witness w = {hv}");
        assert!(
            hv > 0,
            "w = 0 leaves no candidate below it; reseed the workload (probability 2^-16)"
        );

        // SAFETY: `hv - 1 < hv < p`, so this is canonical. (`BatchProof` is not `Clone`, so the
        // tamper is in place and then restored — which is strictly better evidence: the restore
        // going green again shows the refusal was caused by THIS byte and nothing else.)
        let bad = unsafe { BabyBear::from_canonical_unchecked(hv - 1) };
        proof.opening_proof.query_pow_witness = bad;
        // ⚑ ASSERT THE MUTATION HAPPENED before reading the verdict. A falsifier that silently
        // stopped mutating is a green gate with no adversary in it.
        assert_ne!(
            proof.opening_proof.query_pow_witness, honest,
            "the mutation must actually change the witness"
        );

        let verdict = verify_vm_descriptor2_with_config(&w.desc, &proof, &w.pis, &config);
        println!("  w-1 = {} → {verdict:?}", hv - 1);
        let err = verdict.expect_err("a sub-minimal witness MUST be refused");
        assert!(
            err.contains("InvalidPowWitness"),
            "expected the grinding gate to be the refusing check, got: {err}"
        );

        // Restore: the same object goes green again, so the refusal above is attributable to the
        // one field that moved.
        proof.opening_proof.query_pow_witness = honest;
        verify_vm_descriptor2_with_config(&w.desc, &proof, &w.pis, &config)
            .expect("restoring the honest witness restores the accept");
        println!(
            "  ✓ the 16-bit query-PoW predicate is CHECKED, and the check refuses. Every candidate\n\
             \x20   below the minimal witness is invalid by construction, so this tooth cannot go\n\
             \x20   vacuous the way a probabilistic mutation can."
        );
    }

    /// ⚑ **§G7 — BYTE-FOR-BYTE, ON REAL SERIALIZED PROOFS.** §G6 shows the witness is unchanged and
    /// argues that equal witnesses give equal proofs. This one stops arguing: it proves the same
    /// deployed IR-v2 transfer at `(lb=6, q=19, pow=16)` under **rayon pools of 1, 4 and 12
    /// threads** and asserts the `rmp-serde` bytes are identical, hash and length included.
    ///
    /// Thread count is the axis that matters: a schedule bug leaks into the answer exactly by
    /// making the answer depend on how many workers looked at it. Under upstream's `find_map_any`
    /// this test was *measured* to fail (2026-07-31: three rayon runs, three distinct proof
    /// lengths); under `find_map_first` it passed at 1.00x parallelism; it must still pass now.
    ///
    /// ⚑ **The load-bearing constant is `PRE_FIX_WITNESS = 47,912`**, read off a real deployed
    /// proof at these exact knobs on **2026-08-13, on the `find_map_first` path** (§G5, and the
    /// note's §2 cross-check against the counting config's 11,979 SIMD calls). The grind's ONLY
    /// contribution to a proof is that one field element, so reproducing it post-fix is the
    /// old-path/new-path comparison carried out on a real proof rather than on a test harness.
    ///
    /// ⚠ `PRE_FIX_ZERO_POW_BYTES = 138,220` is **not** a pow=16 figure and must not be read as one
    /// — it is §G4's **arm 1**, which holds `pow = 0` at every `q` so the query slope is free of
    /// the grind's draw. Quoting it as the deployed proof size is a mistake this test made on its
    /// first run (it went red at 138,224 against it) and now exists to prevent: proving the
    /// `pow = 0` rung here re-anchors the WORKLOAD to 2026-08-13, so that when the witness assert
    /// below is green it is green about the GRIND and not about a descriptor that stood still.
    #[test]
    fn g7_proof_bytes_are_identical_under_the_windowed_schedule() {
        /// §G5's honest witness at `(lb=6, q=19, pow=16)`, measured 2026-08-13 on `find_map_first`.
        const PRE_FIX_WITNESS: u64 = 47_912;
        /// §G4 **arm 1** at `(lb=6, q=19, pow=0)`, measured 2026-08-13. A workload anchor, not a
        /// deployed proof size.
        const PRE_FIX_ZERO_POW_BYTES: usize = 138_220;
        /// The deployed `(lb=6, q=19, pow=16)` proof, recorded 2026-08-14 on the windowed path.
        /// Not evidence about the fix — a forward regression pin, so the next schedule change has
        /// the golden this one had to reconstruct.
        const DEPLOYED_BYTES: usize = 138_224;
        const DEPLOYED_BLAKE3: &str =
            "3cad30a69901631b78c503c97a9cc7c4d78433d828490a5334e0679e90969033";

        let w = transfer_workload();
        let config = create_config_with_fri(6, 0, 3, 19, 16);
        let mem_boundary = MemBoundaryWitness::default();
        let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

        let max_threads = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(8);
        let mut thread_counts = vec![1usize, 4];
        if max_threads > 4 {
            thread_counts.push(max_threads);
        }
        thread_counts.retain(|&t| t <= max_threads.max(1));
        thread_counts.dedup();

        println!("\n═══ §G7  THE PROOF BYTES DID NOT MOVE ═══\n");
        println!(
            "  {:<10}{:>16}{:>14}  {}",
            "threads", "pow witness", "bytes", "blake3(proof)[..16]"
        );
        println!("  {}", "-".repeat(72));

        let mut seen: Vec<(usize, u64, usize, String)> = Vec::new();
        for &t in &thread_counts {
            let p = pool(t);
            let proof = p.install(|| {
                prove_vm_descriptor2_with_config(
                    &w.desc,
                    &w.base_trace,
                    &w.pis,
                    &mem_boundary,
                    &map_heaps,
                    &config,
                )
                .expect("honest prove")
            });
            verify_vm_descriptor2_with_config(&w.desc, &proof, &w.pis, &config)
                .expect("the honest proof verifies");
            let witness = proof.opening_proof.query_pow_witness.as_canonical_u64();
            let bytes = rmp_serde::to_vec(&proof).expect("serialize");
            let digest = blake3::hash(&bytes).to_hex().to_string();
            println!(
                "  {:<10}{:>16}{:>14}  {}",
                t,
                witness,
                bytes.len(),
                &digest[..16]
            );
            seen.push((t, witness, bytes.len(), digest));
        }

        let (t0, w0, n0, ref d0) = seen[0].clone();
        for (t, wt, nt, dt) in &seen[1..] {
            assert_eq!(
                (wt, nt, dt),
                (&w0, &n0, d0),
                "the proof produced on {t} threads differs from the one produced on {t0} — the \
                 grind's SCHEDULE has reached its ANSWER, which is exactly what `90680ee7d` and \
                 the windowed min are both built not to do"
            );
        }
        println!(
            "\n  ✓ {} pools, one proof: witness {w0}, {n0} bytes, blake3 {d0}",
            seen.len()
        );

        // ── the workload anchor: pow = 0, so the grind contributes nothing at all ────────────
        let zero_config = create_config_with_fri(6, 0, 3, 19, 0);
        let zero_proof = prove_vm_descriptor2_with_config(
            &w.desc,
            &w.base_trace,
            &w.pis,
            &mem_boundary,
            &map_heaps,
            &zero_config,
        )
        .expect("pow=0 prove");
        let zero_bytes = rmp_serde::to_vec(&zero_proof).expect("serialize").len();
        assert_eq!(
            zero_bytes, PRE_FIX_ZERO_POW_BYTES,
            "the pow=0 proof is {zero_bytes} bytes against §G4 arm 1's {PRE_FIX_ZERO_POW_BYTES} \
             from 2026-08-13. The grind cannot touch a pow=0 proof (`grind` returns F::ZERO before \
             searching anything), so this is the DESCRIPTOR / TRACE / FRI config having moved. \
             Re-anchor the constants below before reading them as evidence about the schedule."
        );
        println!(
            "  ✓ workload anchor: the pow=0 rung is still {zero_bytes} B, exactly §G4 arm 1's \
             2026-08-13 figure"
        );

        // ── the grind's answer: the ONE field element the schedule could have moved ──────────
        assert_eq!(
            w0, PRE_FIX_WITNESS,
            "the deployed prover's PoW witness moved from the pre-fix {PRE_FIX_WITNESS} to {w0}. \
             The anchor above says the workload did not move, so this is the windowed min failing \
             to return the MINIMAL witness — the fix is NOT free and every proof byte has moved."
        );
        println!(
            "  ✓ the witness is {w0} — the integer §G5 read off the PRE-FIX `find_map_first` path\n\
             \x20   on 2026-08-13. The schedule changed; the answer did not."
        );

        // The witness is the only wire difference between the two rungs, which is what makes 16
        // soundness bits free on the wire. §G4 measured this as ≤ 8 B across the whole ladder.
        let delta = n0.abs_diff(zero_bytes);
        assert!(
            delta <= 8,
            "pow=16 and pow=0 proofs differ by {delta} B; the witness is one varint field element, \
             so anything above ~8 B means the grind changed more than the witness"
        );
        println!(
            "  ✓ pow=16 vs pow=0 differ by {delta} B — one varint field element, the entire wire \
             cost of 16 soundness bits"
        );

        assert_eq!(
            (n0, d0.as_str()),
            (DEPLOYED_BYTES, DEPLOYED_BLAKE3),
            "the deployed proof no longer matches its 2026-08-14 golden. If the anchor and the \
             witness above are green, the grind is fine and something else in the prover moved."
        );
    }

    #[test]
    #[ignore = "MEASUREMENT: real proofs at five (pow,q) points. --ignored --nocapture"]
    fn g4_pow_vs_queries_at_fixed_soundness() {
        let reps: usize = std::env::var("DREGG_PROFILE_REPS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(5);
        let lb = 6usize;
        let target = column_bits("UDR", lb, 19, 16);
        let w = transfer_workload();
        let rate = packed_rate_ns();

        println!("\n═══ §G4  POW vs QUERIES AT A FIXED SOUNDNESS COLUMN ═══\n");
        println!(
            "  lb = {lb} fixed. `q` chosen so the UDR column ≥ the DEPLOYED UDR column \
             ({target:.4} bits).\n\
             \x20 min of {reps}; RAYON_NUM_THREADS = {}; packed Poseidon2 rate = {rate:.0} ns/call.\n\
             \x20 ⚠ prove_ms INCLUDES the descriptor_ir2 self-verify. The `grind draw` column is ONE\n\
             \x20   sample of an exponential; `E[grind]` is what a cost comparison may use.\n",
            std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "all".into()),
        );

        // Arm 1: pow = 0 at every q. Clean, draw-free prover cost as a function of q alone.
        println!("  ── arm 1: pow = 0, q varying — the DRAW-FREE cost of a query ──");
        println!(
            "  {:<8}{:>8}{:>14}{:>14}{:>14}{:>14}",
            "pow", "q", "UDR bits", "prove ms", "verify ms", "bytes"
        );
        println!("  {}", "-".repeat(72));
        let mut arm1: Vec<Row> = Vec::new();
        for pow in [0usize, 8, 12, 16, 20] {
            let q = queries_for("UDR", lb, pow, target);
            let r = measure(&w, lb, q, 0, reps);
            println!(
                "  {:<8}{:>8}{:>14.3}{:>14.2}{:>14.2}{:>14}",
                format!("0/{pow}"),
                q,
                column_bits("UDR", lb, q, pow),
                r.prove_ms,
                r.verify_ms,
                r.bytes
            );
            arm1.push(r);
        }

        // Arm 2: the real configured point, grind included.
        println!("\n  ── arm 2: the real (pow, q) point ──");
        println!(
            "  {:<8}{:>8}{:>14}{:>14}{:>14}{:>14}{:>16}",
            "pow", "q", "UDR bits", "prove ms", "verify ms", "bytes", "E[grind] ms"
        );
        println!("  {}", "-".repeat(90));
        let mut arm2: Vec<Row> = Vec::new();
        for pow in [0usize, 8, 12, 16, 20] {
            let q = queries_for("UDR", lb, pow, target);
            let r = measure(&w, lb, q, pow, reps);
            let e_grind = if pow == 0 {
                0.0
            } else {
                2f64.powi(pow as i32) / Pack::WIDTH as f64 * rate / 1e6
            };
            println!(
                "  {:<8}{:>8}{:>14.3}{:>14.2}{:>14.2}{:>14}{:>16.2}",
                pow,
                q,
                column_bits("UDR", lb, q, pow),
                r.prove_ms,
                r.verify_ms,
                r.bytes,
                e_grind
            );
            arm2.push(r);
        }

        println!("\n  ── the decision column: EXPECTED total, arm1 (draw-free) + E[grind] ──");
        println!(
            "  {:<8}{:>8}{:>16}{:>16}{:>16}{:>14}{:>14}",
            "pow", "q", "prove−grind ms", "E[grind] ms", "E[prove] ms", "verify ms", "bytes"
        );
        println!("  {}", "-".repeat(94));
        for (i, pow) in [0usize, 8, 12, 16, 20].iter().enumerate() {
            let e_grind = if *pow == 0 {
                0.0
            } else {
                2f64.powi(*pow as i32) / Pack::WIDTH as f64 * rate / 1e6
            };
            println!(
                "  {:<8}{:>8}{:>16.2}{:>16.2}{:>16.2}{:>14.2}{:>14}",
                pow,
                arm1[i].q,
                arm1[i].prove_ms,
                e_grind,
                arm1[i].prove_ms + e_grind,
                arm1[i].verify_ms,
                arm1[i].bytes
            );
        }
        println!(
            "\n  (arm2's `prove ms` is arm1's plus ONE draw of the grind; the two arms together\n\
             \x20 check that the grind is additive and phase-independent.)"
        );
        // ⚑ `pow` costs ONE FIELD ELEMENT on the wire — not zero bytes, and the difference is a
        // real measurement rather than a rounding: `rmp-serde` varint-encodes the witness, so a
        // 16-bit-ground witness (≈2^16) and a `pow=0` witness (`F::ZERO`) differ by a byte or two.
        // Measured 2026-08-14: |Δ| ≤ 4 B on a ~140 KiB proof. The first draft of this test asserted
        // exact equality and went red at 190654 vs 190652, which is the assertion being wrong, not
        // the prover.
        let mut worst = 0i64;
        for (a, b) in arm1.iter().zip(arm2.iter()) {
            assert_eq!(a.q, b.q);
            let d = (b.bytes as i64 - a.bytes as i64).abs();
            worst = worst.max(d);
            assert!(
                d <= 8,
                "pow must not change proof SIZE beyond the witness element at pow={}: {} vs {}",
                b.pow,
                a.bytes,
                b.bytes
            );
        }
        println!(
            "  ✓ proof bytes move by at most {worst} B between the arms across the whole ladder:\n\
             \x20   the grind witness is ONE field element, so `pow` is free on the wire while a\n\
             \x20   query costs ~5.8 KiB."
        );
    }
}
