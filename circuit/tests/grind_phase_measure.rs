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

/// **Strategy A — DEPLOYED.** `(0..num_batches).into_par_iter().find_map_first(..)`, i.e. exactly
/// `DuplexChallenger::grind`.
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

/// **Strategy C — PROPOSED: WINDOWED PARALLEL MIN.** Scan a bounded window of `window` batches
/// **completely** and in parallel, and reduce with `min`. If the window holds a match, its minimum
/// IS the global minimum, so this returns **byte-for-byte the same witness as Strategy A** — same
/// predicate, same soundness, same proof bytes; only the schedule changes. If it holds none,
/// advance to the next window (probability `e^(−window·lanes/2^bits)` per window).
///
/// The point: every window is a FULL parallel scan with no early exit, so it saturates `T` threads,
/// and the work is bounded by a whole number of windows instead of by a geometric draw.
fn grind_windowed(ch: &Ch, bits: usize, window: u64) -> (BabyBear, u64) {
    let (st, widx) = base_state(ch);
    let mask = (1u64 << bits) - 1;
    let num_batches = BabyBear::ORDER_U64.div_ceil(Pack::WIDTH as u64);
    let perm = ch.permutation.clone();
    let mut lo = 0u64;
    let mut windows = 0u64;
    loop {
        let hi = (lo + window).min(num_batches);
        windows += 1;
        let found = (lo..hi)
            .into_par_iter()
            .filter_map(|b| scan_batch(&perm, &st, widx, b, mask))
            .min_by_key(|w| w.as_canonical_u64());
        if let Some(w) = found {
            return (w, windows);
        }
        assert!(hi < num_batches, "no witness in the field");
        lo = hi;
    }
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

    // window sized so ~4 expected matches land in it: P(empty) = e^-4 ≈ 1.8%.
    let window = (4u64 << bits) / Pack::WIDTH as u64;

    /// One (strategy, threads) cell: wall clock AND the contention-free critical path.
    fn cell<F: Fn() -> BabyBear + Send + Sync>(t: usize, reps: usize, f: F) -> (f64, u64, u64) {
        let ms = time_it(t, reps, &f);
        let p = pool(t);
        reset_batches();
        std::hint::black_box(p.install(&f));
        let (total, max) = read_batches();
        (ms, total, max)
    }

    println!(
        "  ── wall clock (min of {reps}) AND the contention-free critical path ──\n\
         \x20 `crit` = max batches scanned by any ONE worker = the permutations on the critical\n\
         \x20 path. `scale` = crit(T=1)/crit(T), the speedup on an IDLE machine.\n"
    );
    println!(
        "  {:<8}| {:>9}{:>7}{:>7} | {:>9}{:>7}{:>7} | {:>9}{:>7}{:>7}",
        "threads", "A ms", "crit", "scale", "B ms", "crit", "scale", "C ms", "crit", "scale"
    );
    println!("  {}", "-".repeat(90));
    let mut base_crit = (1u64, 1u64, 1u64);
    let mut totals = Vec::new();
    for (i, &t) in threads.iter().enumerate() {
        let (a, at, ac) = cell(t, reps, || grind_first(&ch, bits));
        let (b, bt, bc) = cell(t, reps, || grind_any(&ch, bits));
        let (c, ct, cc) = cell(t, reps, || grind_windowed(&ch, bits, window).0);
        if i == 0 {
            base_crit = (ac.max(1), bc.max(1), cc.max(1));
        }
        println!(
            "  {:<8}| {:>9.2}{:>7}{:>7.2} | {:>9.2}{:>7}{:>7.2} | {:>9.2}{:>7}{:>7.2}",
            t,
            a,
            ac,
            base_crit.0 as f64 / ac.max(1) as f64,
            b,
            bc,
            base_crit.1 as f64 / bc.max(1) as f64,
            c,
            cc,
            base_crit.2 as f64 / cc.max(1) as f64,
        );
        totals.push((t, at, bt, ct));
    }
    println!("\n  TOTAL batches scanned (the energy bill, not the latency):");
    println!(
        "  {:<10}{:>16}{:>16}{:>16}",
        "threads", "A first", "B any", "C windowed"
    );
    for (t, at, bt, ct) in &totals {
        println!("  {:<10}{:>16}{:>16}{:>16}", t, at, bt, ct);
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

    // The windowed strategy's work distribution: whole windows, not a geometric tail. The window
    // constant `c` (window covers `c·2^bits` candidates) trades wasted work against the number of
    // synchronisation barriers, so it is swept rather than asserted.
    println!("\n  ── strategy C: the window constant `c` (window covers c·2^bits candidates) ──");
    println!(
        "  {:<8}{:>14}{:>16}{:>18}{:>22}",
        "c", "ms @1 thread", "ms @max", "speedup", "windows over 64 draws"
    );
    println!("  {}", "-".repeat(80));
    for c in [1u64, 2, 4, 8] {
        let win = (c << bits) / Pack::WIDTH as u64;
        let t1 = time_it(1, reps, || grind_windowed(&ch, bits, win).0);
        let tm = time_it(max_threads, reps, || grind_windowed(&ch, bits, win).0);
        let mut wins = std::collections::BTreeMap::new();
        for s in 0..64u64 {
            let cc = seeded_challenger(s.wrapping_mul(0x1234_5678_9ABC_DEF1));
            let (_, n) = grind_windowed(&cc, bits, win);
            *wins.entry(n).or_insert(0usize) += 1;
        }
        println!(
            "  {:<8}{:>14.2}{:>16.2}{:>18.2}{:>22}",
            c,
            t1,
            tm,
            t1 / tm,
            format!("{wins:?}")
        );
    }
    println!(
        "  (⇒ latency is QUANTISED in whole windows with a geometric TAIL IN WINDOW COUNT, not in\n\
         \x20 candidates: `P(> n windows) = e^(−c·n)`, so the p99 is a small integer multiple of a\n\
         \x20 fixed, parallel, predictable unit rather than 4.6× the mean.)"
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
    fn packed_rate_ns() -> f64 {
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
