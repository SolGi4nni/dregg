//! # THE BN254 OUTER GRIND — the same pathology, at ~100× the per-candidate price
//!
//! `notes/grind-phase.md` §0b measured the BabyBear leaf grind and flagged, without measuring it,
//! that `MultiField32Challenger::grind` — the **outer/shrink** challenger, the one the apex and
//! gnark byte-parity gates ride on — carried the identical `find_first` pathology at a far higher
//! per-candidate cost:
//!
//! > it is **neither SIMD-packed nor batched**: one candidate costs one whole **BN254 Poseidon2
//! > duplex**, not one BabyBear permutation ÷ 4 lanes.
//!
//! So the leaf's "no parallelism at all" result lands here multiplied by the ratio of a BN254
//! permutation to a packed BabyBear one. This file measures that, and — the part that matters —
//! asserts the windowed schedule returns the **same witness** on this path too.
//!
//! ⚑ **Operation counts, not wall clock.** Every number that carries a claim below is a count of
//! `check_witness` calls (each one BN254 duplex). This box runs at load average 20–100 with ~40
//! login sessions; the one timed column is labelled and is an upper bound.
//!
//! ```text
//! cargo test -p dregg-circuit-prove --release --test outer_grind_schedule -- --nocapture
//! ```
//! The thread-scaling measurement is `#[ignore]`d (minutes of BN254 permutations); add `--ignored`.

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use dregg_circuit_prove::dregg_outer_config::{
    OUTER_FRI_QUERY_POW_BITS, OuterChallenger, dregg_poseidon2_bn254,
};
use p3_baby_bear::BabyBear;
use p3_challenger::{CanObserve, GrindingChallenger, default_grind_window};
use p3_field::PrimeCharacteristicRing;
use p3_field::integers::QuotientMap;
use p3_field::{PrimeField32, PrimeField64};
use rayon::prelude::*;

/// A challenger whose transcript is `seed`. Distinct seeds are independent grind draws.
fn seeded_outer(seed: u64) -> OuterChallenger {
    let mut ch = OuterChallenger::new(dregg_poseidon2_bn254())
        .expect("BabyBear order < BN254 order, RATE < WIDTH");
    ch.observe(BabyBear::from_u64(seed % BabyBear::ORDER_U64));
    ch.observe(BabyBear::from_u64((seed >> 31) % BabyBear::ORDER_U64));
    ch
}

// ── the contention-free instrument: one counter per rayon worker ─────────────────────────────
#[repr(align(128))]
struct PaddedCounter(AtomicU64);
static CALLS: [PaddedCounter; 64] = [const { PaddedCounter(AtomicU64::new(0)) }; 64];

fn bump() {
    let i = rayon::current_thread_index().unwrap_or(63).min(63);
    CALLS[i].0.fetch_add(1, Ordering::Relaxed);
}

fn reset_calls() {
    for c in CALLS.iter() {
        c.0.store(0, Ordering::Relaxed);
    }
}

/// `(total check_witness calls, max on any one worker)`. Each call is one BN254 duplex, so the
/// second number IS the critical path in BN254 permutations.
fn read_calls() -> (u64, u64) {
    let v: Vec<u64> = CALLS.iter().map(|c| c.0.load(Ordering::Relaxed)).collect();
    (v.iter().sum(), v.iter().copied().max().unwrap_or(0))
}

/// **BEFORE.** `MultiField32Challenger::grind`'s body as it stood between `90680ee7d` and the
/// 2026-08-14 schedule fix. Kept as the differential oracle for the code that is no longer there.
fn grind_first(ch: &OuterChallenger, bits: usize) -> BabyBear {
    (0..BabyBear::ORDER_U32)
        .into_par_iter()
        .map(|i| unsafe { BabyBear::from_canonical_unchecked(i) })
        .find_first(|witness| {
            bump();
            ch.clone().check_witness(bits, *witness)
        })
        .expect("failed to find witness")
}

/// **AFTER.** The LANDED schedule — `p3_challenger::windowed_find_map_first` itself, the function
/// `MultiField32Challenger::grind` now calls. Only the counter is local.
fn grind_windowed(ch: &OuterChallenger, bits: usize, window: u64) -> BabyBear {
    p3_challenger::windowed_find_map_first(u64::from(BabyBear::ORDER_U32), window, |i| {
        bump();
        // SAFETY: `i < BabyBear::ORDER_U32` by construction.
        let witness = unsafe { BabyBear::from_canonical_unchecked(i as u32) };
        ch.clone().check_witness(bits, witness).then_some(witness)
    })
    .expect("failed to find witness")
}

fn pool(n: usize) -> rayon::ThreadPool {
    rayon::ThreadPoolBuilder::new()
        .num_threads(n)
        .build()
        .expect("pool")
}

/// ⚑ **THE CORRECTNESS OBLIGATION ON THE OUTER PATH.** Same three checks as the leaf's §G6, and
/// they matter more here: this is the challenger the apex/shrink/gnark byte-parity gates ride on,
/// so if the schedule reached the answer anywhere it would show up as a moved apex proof.
///
/// Runs at `bits = 12` rather than the deployed 16 because a candidate here is a whole BN254
/// duplex: `2^12` of them is a second of work and `2^16` is a minute, and the property under test
/// (does the schedule move the answer?) is not `bits`-specific — the window sweep covers the
/// `bits`-dependent arithmetic separately, and one draw at the deployed 16 is asserted too.
#[test]
fn outer_windowed_grind_returns_the_old_paths_witness() {
    let bits = 12usize;
    let n: u64 = std::env::var("DREGG_OUTER_PARITY_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(12);

    println!("\n═══ THE BN254 OUTER GRIND RETURNS THE OLD PATH'S WITNESS ═══\n");

    // ── 1. old path vs new path ───────────────────────────────────────────────────────────────
    for s in 0..n {
        let seed = s.wrapping_mul(0x9E37_79B9_7F4A_7C15);
        let ch = seeded_outer(seed);
        let old = grind_first(&ch, bits);
        let new = ch.clone().grind(bits);
        assert_eq!(
            old, new,
            "seed={seed}: the windowed schedule returned a DIFFERENT witness than `find_first` on \
             the OUTER challenger — the apex/shrink proof bytes have moved"
        );
    }
    println!(
        "  bits = {bits}: {n} transcripts, old `find_first` == new windowed grind on every one"
    );

    // ── 2. the CONTRACT, exhaustively ─────────────────────────────────────────────────────────
    let ch = seeded_outer(0x0A7E_2A11_u64);
    let w = ch.clone().grind(bits).as_canonical_u64();
    let lower_hit = (0..w).into_par_iter().any(|c| {
        // SAFETY: `c < w < p`.
        let cand = unsafe { BabyBear::from_canonical_unchecked(c as u32) };
        ch.clone().check_witness(bits, cand)
    });
    assert!(
        !lower_hit,
        "a candidate below the returned witness {w} satisfies the outer PoW predicate — `grind` is \
         not returning the MINIMAL witness"
    );
    println!(
        "    minimality verified EXHAUSTIVELY: all {w} candidates below the witness are invalid"
    );

    // ── 3. window invariance ──────────────────────────────────────────────────────────────────
    let reference = ch.clone().grind(bits);
    for window in [1u64, 7, 64, 1000, 4096, 65_536, 1 << 20] {
        assert_eq!(
            ch.clone().grind_with_window(bits, window),
            reference,
            "window {window} changed the outer witness — the window is supposed to be unable to \
             reach the answer"
        );
    }
    println!(
        "    window invariance: 7 window sizes from 1 to 2^20 all returned {}",
        reference.as_canonical_u64()
    );

    // ── 4. one draw at the DEPLOYED bits, because that is the number that ships ────────────────
    let deployed = OUTER_FRI_QUERY_POW_BITS;
    let ch16 = seeded_outer(0xDEB0_1DED_u64);
    let old16 = grind_first(&ch16, deployed);
    let new16 = ch16.clone().grind(deployed);
    assert_eq!(
        old16, new16,
        "at the DEPLOYED OUTER_FRI_QUERY_POW_BITS = {deployed} the schedules disagree"
    );
    println!(
        "  bits = {deployed} (DEPLOYED): old == new == {}",
        new16.as_canonical_u64()
    );
}

/// ⚑ **DOES THE OUTER GRIND PARALLELISE?** The leaf's answer was *no, scale 1.00*. This measures
/// the same question where a candidate is a BN254 duplex.
#[test]
#[ignore = "MEASUREMENT: whole BN254 grinds across thread counts. --ignored --nocapture"]
fn outer_grind_thread_scaling() {
    let bits: usize = std::env::var("DREGG_OUTER_GRIND_BITS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(12);
    let reps: usize = std::env::var("DREGG_OUTER_GRIND_REPS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(3);
    let max_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8);

    // One fixed transcript, so every strategy and thread count faces the same draw.
    let ch = seeded_outer(0x5EED_0F17_u64);
    let w_ref = grind_first(&ch, bits);
    // ⚑ PIN THE ORACLE TO REALITY. If the `find_first` copy above has drifted from the code it
    // stands for, every BEFORE number here is a paraphrase.
    assert_eq!(
        w_ref,
        ch.clone().grind(bits),
        "the `find_first` oracle must agree with the deployed grind on this transcript"
    );
    let window = default_grind_window(bits, 1);

    println!("\n═══ THE BN254 OUTER GRIND: DOES IT PARALLELISE? ═══\n");
    println!(
        "  bits = {bits}, min of {reps}, box parallelism = {max_threads}, window = {window} \
         candidates\n\
         \x20 fixed transcript: minimal witness = {}, so the BEFORE path walks {} candidates\n\
         \x20 ⚑ ONE CANDIDATE = ONE BN254 POSEIDON2 DUPLEX. No SIMD, no batching — the leaf's\n\
         \x20   packed BabyBear batch covers 4 candidates for ~758 ns; here 1 costs ~{:.1} µs.\n",
        w_ref.as_canonical_u64(),
        w_ref.as_canonical_u64() + 1,
        {
            let t0 = Instant::now();
            let probe = seeded_outer(1);
            for i in 0..256u32 {
                let cand = unsafe { BabyBear::from_canonical_unchecked(i) };
                std::hint::black_box(probe.clone().check_witness(bits, cand));
            }
            t0.elapsed().as_secs_f64() * 1e6 / 256.0
        }
    );

    fn time_it<F: Fn() -> BabyBear + Send + Sync>(t: usize, reps: usize, f: F) -> f64 {
        let p = pool(t);
        let mut best = f64::INFINITY;
        for _ in 0..reps {
            let t0 = Instant::now();
            let w = p.install(&f);
            best = best.min(t0.elapsed().as_secs_f64() * 1000.0);
            std::hint::black_box(w);
        }
        best
    }

    fn cell<F: Fn() -> BabyBear + Send + Sync>(t: usize, reps: usize, f: F) -> (f64, u64, u64) {
        let ms = time_it(t, reps, &f);
        let p = pool(t);
        reset_calls();
        std::hint::black_box(p.install(&f));
        let (total, max) = read_calls();
        (ms, total, max)
    }

    let mut threads: Vec<usize> = vec![1, 4];
    if max_threads > 4 {
        threads.push(max_threads);
    }
    threads.retain(|&t| t <= max_threads.max(1));
    threads.dedup();

    println!(
        "  ── EXACT OPERATION COUNTS (calls = BN254 duplexes; no clock) ──\n\
         \x20 `crit` = calls on the busiest worker = the CRITICAL PATH. `total` = the WORK.\n"
    );
    println!(
        "  {:<9}| {:>10}{:>8}{:>12} | {:>10}{:>8}{:>12}",
        "threads", "BEFORE crit", "scale", "BEFORE total", "AFTER crit", "scale", "AFTER total"
    );
    println!("  {}", "-".repeat(80));
    let mut base = (1u64, 1u64);
    let mut rows = Vec::new();
    for (i, &t) in threads.iter().enumerate() {
        let (a_ms, a_tot, a_crit) = cell(t, reps, || grind_first(&ch, bits));
        let (c_ms, c_tot, c_crit) = cell(t, reps, || grind_windowed(&ch, bits, window));
        if i == 0 {
            base = (a_crit.max(1), c_crit.max(1));
        }
        println!(
            "  {:<9}| {:>10}{:>8.2}{:>12} | {:>10}{:>8.2}{:>12}",
            t,
            a_crit,
            base.0 as f64 / a_crit.max(1) as f64,
            a_tot,
            c_crit,
            base.1 as f64 / c_crit.max(1) as f64,
            c_tot,
        );
        rows.push((t, a_ms, c_ms, a_crit, c_crit, a_tot, c_tot));
    }

    let (_, _, _, crit_base, _, work_base, _) = rows[0];
    println!(
        "\n  ⚑ BEFORE vs AFTER against the old path's own best case \
         ({crit_base} calls critical, {work_base} total, at 1 thread):"
    );
    println!(
        "  {:<9}{:>14}{:>14}{:>10}{:>16}{:>12}",
        "threads", "crit BEFORE", "crit AFTER", "crit ×", "work AFTER", "work × A@1"
    );
    for (t, _, _, a_crit, c_crit, _, c_tot) in &rows {
        println!(
            "  {:<9}{:>14}{:>14}{:>10.2}{:>16}{:>12.2}",
            t,
            a_crit,
            c_crit,
            *a_crit as f64 / (*c_crit).max(1) as f64,
            c_tot,
            *c_tot as f64 / work_base.max(1) as f64,
        );
    }
    println!(
        "  ⚠ crit is a LATENCY ratio and work is a THROUGHPUT ratio. Different units; never\n\
         \x20 multiply them into one figure."
    );

    println!("\n  ── wall clock, min of {reps} ──  ⚠ contended upper bound, not evidence");
    println!("  {:<9}{:>14}{:>14}", "threads", "BEFORE ms", "AFTER ms");
    for (t, a_ms, c_ms, ..) in &rows {
        println!("  {:<9}{:>14.2}{:>14.2}", t, a_ms, c_ms);
    }

    // The claim that makes this a scheduling change on the outer path too.
    assert_eq!(
        grind_windowed(&ch, bits, window),
        w_ref,
        "the outer windowed min must return the same witness as `find_first`"
    );
}
