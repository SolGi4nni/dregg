//! # E4 — THE FRI RE-GRID MEASUREMENT at post-S2 / mocked-floor widths (PRE-FREEZE)
//!
//! `ir2_config`'s `(log_blowup 6, 19 queries, pow 16)` point was tuned when the member proof was
//! 120.4 KiB. Post-S2 it is 375 KB (main 1704×64, chip 386×256, range 16; 394,400 committed
//! cells — `docs/MEASURE-legacy-1felt-chain-drop.md`), and the Epoch-2 floor (~82.8K cells) moves
//! the knee again: at floor scale the lb-8 LDE volume ≈ today's lb-6 volume (21.2M vs 25.2M
//! cell-evals). This harness is the measurement lane `docs/EFFICIENCY-BACKLOG-circuit-minimality.md`
//! §E4 calls for, run BYTE-SAFE:
//!
//!   * **NO regen, no FS re-pin, no descriptor bytes.** Nothing here mints from any registry —
//!     the traces are MOCKED synthetic-width fixtures (see below). The `(lb,q)` flip itself is a
//!     regen (FS epoch) and is STAGED for the Epoch-2 bundle, not performed here.
//!   * **Every candidate goes through the actual Lean `dregg_fri_ledger`** — the commit-phase
//!     `ε_C` column depends on the trace height and BINDS BELOW the Johnson closed-form at the
//!     deployed wrap, so the two closed-form query columns alone cannot judge a `log_blowup`
//!     move. The verdicts here are the compiled `Dregg2.Circuit.FriLedger.friLedger`'s numbers,
//!     not a Rust re-derivation (there is deliberately no soundness formula in this file).
//!   * The candidate set is the backlog's: `(8,15,16)`, `(8,14,16)` vs the deployed `(6,19,16)`,
//!     PLUS the two never-gridded knobs — `commit_proof_of_work_bits > 0` (hardwired 0 in every
//!     shipped config; unpriced by the ledger — a NAMED residual, `FriLedger.lean`) and
//!     `log_final_poly_len > 0` (echoed on the ledger wire, enters no soundness column).
//!
//! ## The MOCKED shapes (and what each is honest about)
//!
//! ⚑ SUBSTRATE, SAID OUT LOUD: the synthetic descriptors below are MEASUREMENT FIXTURES — cost
//! geometry only, all-zero traces under degree-2 always-satisfied gates. They are NOT authored
//! AIR, ship nowhere, and bind nothing; the deployed AIR stays Lean-authored and untouched.
//!
//!   * **A. post-S2 member main proxy** — W=1704 at h=2^6: the measured post-S2 main table. Its
//!     per-candidate BYTE ratios carry the per-query × width structure of the real member; its
//!     absolute bytes UNDERSTATE the member (no chip/range instances, no permutation columns).
//!   * **B. Epoch-2 floor cell-proxy** — W=1293 at h=2^6 = the ~82.8K-cell floor as one
//!     instance; its lb-8 LDE volume (2^14 × 1293 ≈ 21.2M) is exactly the backlog's arithmetic.
//!   * **C. post-S2 total-cell proxy** — W=6162 at h=2^6 = all 394,400 post-S2 cells as one
//!     instance: the PROVER-COST equivalent of today's whole member (its LDE volume at each lb
//!     matches the real member's total). Its bytes OVERSTATE (the chip's cells ride at 2^8 in
//!     production, not as width); read prover time here, bytes from A.
//!
//! Prover-cost caveat, stated not smuggled: shape A misses the chip instance's own 4× LDE at
//! lb 8 (386×2^8 → 2^16 domain); shape C prices it back in as width. The two bracket the truth.
//!
//! Run the ledger gate (fast, always on):
//!   CARGO_TARGET_DIR=/tmp/adv-E4 cargo test -p dregg-circuit-prove --release \
//!     --test fri_regrid_post_s2_measure -- --nocapture
//! Run the byte/time sweep (SLOW, 21 proves):
//!   CARGO_TARGET_DIR=/tmp/adv-E4 cargo test -p dregg-circuit-prove --release \
//!     --test fri_regrid_post_s2_measure -- --ignored --nocapture

use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, IR2_EXT_DEGREE, IR2_FRI_LOG_BLOWUP, IR2_FRI_LOG_FINAL_POLY_LEN,
    IR2_FRI_MAX_LOG_ARITY, IR2_FRI_NUM_QUERIES, IR2_FRI_QUERY_POW_BITS, MemBoundaryWitness,
    VmConstraint2, prove_vm_descriptor2_with_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};
use dregg_circuit::plonky3_prover::{DreggStarkConfig, create_config_with_fri_full};
use dregg_lean_ffi::{FriKnobs, FriLedger, fri_ledger, fri_ledger_available};
use p3_field::PrimeCharacteristicRing;

// ─────────────────────────────────────────────────────────────────────────────
// The measured shape facts this harness mocks (sources named; nothing derived here).
// ─────────────────────────────────────────────────────────────────────────────

/// Post-S2 main-table width (docs/MEASURE-legacy-1felt-chain-drop.md: "width 2664 → 1704").
const POST_S2_MAIN_WIDTH: usize = 1704;
/// Post-S2 member log2 main height (measured: instance 0 at 2^6).
const MEMBER_LOG_HEIGHT: usize = 6;
/// Post-S2 total committed cells, all instances (measured: 394,400) — shape C's width is
/// this at h=2^6, the prover-cost (LDE-volume) equivalent of the whole member.
const POST_S2_TOTAL_CELLS: usize = 394_400;
/// The Epoch-2 floor's committed-cell total (~82.8K — backlog §E4's 21.2M / 2^8 arithmetic),
/// mocked as one h=2^6 instance.
const FLOOR_CELLS: usize = 82_800;
/// The post-S2 member's TALLEST instance is the 256-row poseidon2 chip, so the member
/// statement's FRI domain is `|D⁽⁰⁾| = 2^(8 + lb)` — at the deployed lb 6 that is the
/// measured `LEAF_ENVELOPE_LOG_D0 = 14` (`fri_trace_height_measure.rs`). ε_C is read THERE.
const POST_S2_CHIP_LOG_HEIGHT: usize = 8;
/// BCIKS20 proximity parameter — the ANALYSIS knob, same value the params gate pins
/// (`fri_params_soundness_budget.rs::BCIKS_M`); Lean refuses m < 3 (Thm 8.3's hypothesis).
const BCIKS_M: usize = 7;

// The CURRENT gate floors, restated from `fri_params_soundness_budget.rs` (lines named there)
// so the teeth below can say WHICH pins the staged cutover must move. They are quoted, not
// re-derived; if the gate's floors move, these literals red and get reconciled by hand.
const CURRENT_JOHNSON_FLOOR_BITS: usize = 71; // fri_params_soundness_budget.rs::JOHNSON_FLOOR_BITS
const CURRENT_PER_FOLD_FLOOR_BITS: usize = 109; // ::PER_FOLD_FLOOR_BITS
const CURRENT_CAPACITY_MARGIN_BITS: usize = 128; // ::CAPACITY_DRIFT_MARGIN_BITS (drift canary, NOT security)

// ─────────────────────────────────────────────────────────────────────────────
// The E4 candidate set.
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Clone, Copy)]
struct Candidate {
    label: &'static str,
    log_blowup: usize,
    num_queries: usize,
    query_pow: usize,
    /// Never-gridded knob #1: final-poly early stop. Echoed by the Lean ledger wire, enters
    /// NO soundness column — a wire/prover-shape knob only.
    log_final_poly_len: usize,
    /// Never-gridded knob #2: plonky3's commit-phase grinding. Zero in every shipped config
    /// and UNPRICED by the ledger (named residual) — measured here for its byte/time cost so
    /// the residual at least stops being uncosted.
    commit_pow: usize,
}

const CANDIDATES: &[Candidate] = &[
    Candidate {
        label: "baseline (6,19,16) [DEPLOYED ir2]",
        log_blowup: 6,
        num_queries: 19,
        query_pow: 16,
        log_final_poly_len: 0,
        commit_pow: 0,
    },
    Candidate {
        label: "regrid (8,15,16)",
        log_blowup: 8,
        num_queries: 15,
        query_pow: 16,
        log_final_poly_len: 0,
        commit_pow: 0,
    },
    Candidate {
        label: "regrid (8,14,16)",
        log_blowup: 8,
        num_queries: 14,
        query_pow: 16,
        log_final_poly_len: 0,
        commit_pow: 0,
    },
    Candidate {
        label: "baseline + lfpl 4",
        log_blowup: 6,
        num_queries: 19,
        query_pow: 16,
        log_final_poly_len: 4,
        commit_pow: 0,
    },
    Candidate {
        label: "regrid (8,15,16) + lfpl 4",
        log_blowup: 8,
        num_queries: 15,
        query_pow: 16,
        log_final_poly_len: 4,
        commit_pow: 0,
    },
    Candidate {
        label: "baseline + commit-pow 8",
        log_blowup: 6,
        num_queries: 19,
        query_pow: 16,
        log_final_poly_len: 0,
        commit_pow: 8,
    },
    Candidate {
        label: "regrid (8,15,16) + commit-pow 8",
        log_blowup: 8,
        num_queries: 15,
        query_pow: 16,
        log_final_poly_len: 0,
        commit_pow: 8,
    },
];

/// The Lean-ledger reading of one candidate at the post-S2 member statement: the FRI domain is
/// set by the TALLEST instance (the 2^8 chip), so `log_d0 = 8 + lb`. The `ε_C` column moves with
/// `lb` through BOTH `2^(3·lb/2)` and `|D⁰|²` — the double penalty the closed forms cannot see.
fn member_knobs(c: &Candidate) -> FriKnobs {
    FriKnobs {
        log_blowup: c.log_blowup,
        num_queries: c.num_queries,
        query_pow_bits: c.query_pow,
        max_log_arity: IR2_FRI_MAX_LOG_ARITY, // the deployed batch fold arity (8) — not re-gridded here
        log_final_poly_len: c.log_final_poly_len,
        ext_deg: IR2_EXT_DEGREE,
        log_d0: POST_S2_CHIP_LOG_HEIGHT + c.log_blowup,
        bciks_m: BCIKS_M,
        // ⚑ The candidate's OWN commit-PoW, on the wire at last. This harness has always carried a
        // `commit_pow` column in its grid and measured its BYTE/TIME cost; until the ledger wire
        // grew this field there was no way to ask Lean what it BUYS, so the grid measured a knob
        // whose whole point is invisible to the verdict beside it.
        commit_pow: c.commit_pow,
    }
}

fn ledger_or_die(c: &Candidate) -> FriLedger {
    fri_ledger(member_knobs(c)).unwrap_or_else(|e| {
        panic!(
            "[{}] the Lean ledger REFUSED this candidate ({e}) — an E4 point with no \
             machine-checked verdict is not a candidate",
            c.label
        )
    })
}

fn require_ledger() {
    assert!(
        fri_ledger_available(),
        "the VERIFIED Lean FRI ledger (`@[export] dregg_fri_ledger`) is not in the linked \
         archive — this harness reports NO candidate without its machine-checked verdict, and \
         it must NOT fall back to Rust arithmetic. Rebuild: `lake build Dregg2.Circuit.FriLedger` \
         in metatheory/, then `cargo build -p dregg-lean-ffi`."
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// TEST 1 (fast, always on): every candidate through the Lean ledger, with the
// cutover-relevant facts asserted — the part of E4 that is pure soundness accounting.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn every_e4_candidate_carries_a_lean_ledger_verdict() {
    require_ledger();

    // The baseline candidate IS the deployed ir2 knob set — pinned here so this harness can
    // never quietly measure against a stale baseline while the deployed consts move.
    let base = &CANDIDATES[0];
    assert_eq!(
        (
            base.log_blowup,
            base.num_queries,
            base.query_pow,
            base.log_final_poly_len
        ),
        (
            IR2_FRI_LOG_BLOWUP,
            IR2_FRI_NUM_QUERIES,
            IR2_FRI_QUERY_POW_BITS,
            IR2_FRI_LOG_FINAL_POLY_LEN
        ),
        "the E4 baseline drifted off the deployed ir2 consts — re-ground the candidate table"
    );

    println!(
        "== E4 LEAN-LEDGER VERDICTS (member statement: log_d0 = {POST_S2_CHIP_LOG_HEIGHT}+lb \
         [chip 2^{POST_S2_CHIP_LOG_HEIGHT} is the tallest post-S2 instance], ext_deg \
         {IR2_EXT_DEGREE}, arity 2^{IR2_FRI_MAX_LOG_ARITY}, bciks_m {BCIKS_M}) =="
    );
    println!(
        "{:<34} {:>3} {:>3} {:>4} {:>5} {:>5} | {:>8} {:>8} {:>9} {:>7}",
        "candidate", "lb", "q", "qpow", "lfpl", "cpow", "per-fold", "johnson", "capacity", "commit"
    );
    let mut ledgers: Vec<FriLedger> = Vec::new();
    for c in CANDIDATES {
        let l = ledger_or_die(c);
        println!(
            "{:<34} {:>3} {:>3} {:>4} {:>5} {:>5} | {:>8} {:>8} {:>9} {:>7}",
            c.label,
            c.log_blowup,
            c.num_queries,
            c.query_pow,
            c.log_final_poly_len,
            c.commit_pow,
            l.per_fold_bits,
            l.johnson_bits,
            l.capacity_bits,
            l.commit_bits,
        );
        ledgers.push(l);
    }
    let (base_l, r15, r14) = (&ledgers[0], &ledgers[1], &ledgers[2]);

    // ── Tooth 1: the two re-grid points clear the CURRENT query floors, per Lean. This is the
    //    admissibility fact the backlog quotes; here it is read off the ledger, not the closed form.
    for (c, l) in [(&CANDIDATES[1], r15), (&CANDIDATES[2], r14)] {
        assert!(
            l.johnson_bits >= CURRENT_JOHNSON_FLOOR_BITS,
            "[{}] Johnson {} fell under the current floor {CURRENT_JOHNSON_FLOOR_BITS}",
            c.label,
            l.johnson_bits
        );
        assert!(
            l.capacity_bits >= CURRENT_CAPACITY_MARGIN_BITS,
            "[{}] capacity {} fell under the {CURRENT_CAPACITY_MARGIN_BITS} drift margin \
             (a REFUTED-conjecture canary, not security — but the gate still pins it)",
            c.label,
            l.capacity_bits
        );
    }
    // (8,14,16) sits at capacity EXACTLY 128 — zero drift headroom, the same posture the old
    // gate flagged on create_recursion_config. Pinned as a fact so the cutover chooses knowingly.
    assert_eq!(
        r14.capacity_bits, CURRENT_CAPACITY_MARGIN_BITS,
        "(8,14,16) was expected at capacity exactly {CURRENT_CAPACITY_MARGIN_BITS} (zero \
         headroom); Lean read {} — re-examine the candidate table",
        r14.capacity_bits
    );

    // ── Tooth 2: at lb 8 the PER-FOLD posture drops BELOW the current 109 floor (|Good| grows
    //    with |κ|² = 2^(2·lb)). So the staged cutover CANNOT be knobs-only: it must re-derive
    //    the per-fold floor at Lean's lb-8 reading AND extend the hΦ fiber discharge
    //    (`FriArityFiberDischarge`) with the (arity 8, lb 8) instance — lb 8 is NOT among the
    //    six configs discharged today. This tooth keeps that Lean work named in the recipe.
    assert!(
        r15.per_fold_bits < CURRENT_PER_FOLD_FLOOR_BITS,
        "expected the lb-8 per-fold posture ({}) below the current floor \
         {CURRENT_PER_FOLD_FLOOR_BITS}; if this inverted, the cutover recipe's floor-move step \
         is stale",
        r15.per_fold_bits
    );
    assert_eq!(
        r15.per_fold_bits, r14.per_fold_bits,
        "per-fold is query-independent (query_ledger_does_not_determine_perFold) — two lb-8 \
         candidates must read the same column"
    );

    // ── Tooth 3: THE ε_C FINDING — the reason the ledger runs at all. lb 6→8 on the member
    //    statement moves ε_C through 2^(3·lb/2) AND |D⁰|² (log_d0 = 8+lb rises with lb), so the
    //    commit column falls STRICTLY while both closed-form query columns of (8,15,16) look
    //    fine. Whoever lands the cutover prices THIS, not just the 136/76.
    assert!(
        r15.commit_bits < base_l.commit_bits,
        "the commit-phase column was expected to fall under lb 6→8 (ε_C ∝ 2^(3lb/2)·|D⁰|²); \
         Lean read {} vs baseline {} — if this inverted, the E4 write-up's ε_C caveat is stale",
        r15.commit_bits,
        base_l.commit_bits
    );
    println!(
        "ε_C VERDICT: lb 6→8 costs the member statement {} commit-phase bits ({} → {}) — the \
         cost the Johnson/capacity closed forms CANNOT see; compensating levers are ext_deg \
         (+~31 bits/degree) or the unpriced commit-pow knob below.",
        base_l.commit_bits - r15.commit_bits,
        base_l.commit_bits,
        r15.commit_bits
    );

    // ── Tooth 4: the two never-gridded knobs are LEDGER-INVISIBLE, and that is a stated fact,
    //    not an oversight: lfpl is echoed into no column; commit-pow is a NAMED residual the
    //    ledger deliberately does not price (`FriLedger.lean`'s "unpriced" block). Their twins
    //    must therefore read IDENTICAL ledgers — any drift means the ledger started pricing
    //    one of them and this harness's labels are stale.
    for (twin, base_idx, knob) in [
        (&ledgers[3], 0usize, "log_final_poly_len"),
        (&ledgers[4], 1, "log_final_poly_len"),
        (&ledgers[5], 0, "commit_proof_of_work_bits"),
        (&ledgers[6], 1, "commit_proof_of_work_bits"),
    ] {
        assert_eq!(
            (
                twin.per_fold_bits,
                twin.johnson_bits,
                twin.capacity_bits,
                twin.commit_bits
            ),
            (
                ledgers[base_idx].per_fold_bits,
                ledgers[base_idx].johnson_bits,
                ledgers[base_idx].capacity_bits,
                ledgers[base_idx].commit_bits
            ),
            "{knob} moved a ledger column — the ledger began pricing a knob this harness \
             documents as unpriced; reconcile the labels before trusting either"
        );
    }
    println!(
        "never-gridded knobs: ledger-invisible as documented (lfpl enters no column; commit-pow \
         is the NAMED UNPRICED residual — its grinding buys ε_C headroom no theorem here counts)."
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// TEST 2 (SLOW, --ignored): the byte/prover-cost sweep over the mocked widths.
// ─────────────────────────────────────────────────────────────────────────────

/// A measurement fixture, not an AIR: `width` columns, every adjacent pair constrained by a
/// degree-2 always-satisfied gate (`col_i · col_{i+1} = 0` on the all-zero trace), so every
/// column is genuinely committed AND read by the quotient, with zero authored semantics.
fn mock_member(width: usize, name: &str) -> EffectVmDescriptor2 {
    let constraints = (0..width.saturating_sub(1))
        .map(|i| {
            VmConstraint2::Base(VmConstraint::Gate(LeanExpr::Mul(
                Box::new(LeanExpr::Var(i)),
                Box::new(LeanExpr::Var(i + 1)),
            )))
        })
        .collect();
    EffectVmDescriptor2 {
        name: name.to_string(),
        trace_width: width,
        public_input_count: 0,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

struct Shape {
    label: &'static str,
    width: usize,
    log_height: usize,
    /// What this shape is honest about (printed with every row so no number travels naked).
    honest_about: &'static str,
}

fn shapes() -> Vec<Shape> {
    vec![
        Shape {
            label: "A post-S2 main proxy",
            width: POST_S2_MAIN_WIDTH,
            log_height: MEMBER_LOG_HEIGHT,
            honest_about: "byte RATIOS (per-query × width structure); absolute bytes understate \
                           the member (no chip/range/perm instances)",
        },
        Shape {
            label: "B floor cell-proxy",
            width: FLOOR_CELLS >> MEMBER_LOG_HEIGHT,
            log_height: MEMBER_LOG_HEIGHT,
            honest_about: "the Epoch-2 ~82.8K-cell floor as one instance; its lb-8 LDE volume is \
                           the backlog's 21.2M arithmetic",
        },
        Shape {
            label: "C post-S2 total-cell proxy",
            width: POST_S2_TOTAL_CELLS >> MEMBER_LOG_HEIGHT,
            log_height: MEMBER_LOG_HEIGHT,
            honest_about: "PROVER COST (LDE volume = the whole member's); bytes overstate (chip \
                           cells ride as width here)",
        },
    ]
}

#[test]
#[ignore = "SLOW: 3 shapes × 7 candidates = 21 real proves (release: ~minutes). Run with --ignored --nocapture; the ledger verdicts run in the always-on test."]
fn fri_regrid_post_s2_mocked_width_measure() {
    require_ledger();

    for shape in shapes() {
        let desc = mock_member(shape.width, shape.label);
        let rows = vec![vec![BabyBear::ZERO; shape.width]; 1 << shape.log_height];
        let mem_boundary = MemBoundaryWitness::default();
        let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

        println!(
            "\n==== SHAPE {}: W={} h=2^{} — honest about: {} ====",
            shape.label, shape.width, shape.log_height, shape.honest_about
        );
        println!(
            "{:<34} {:>11} {:>11} {:>8} {:>7} | {:>7} {:>7}",
            "candidate", "proof_bytes", "vs baseline", "prove", "verify", "johnson", "commit"
        );

        let mut baseline_bytes: Option<usize> = None;
        let mut tamper_checked = false;

        for c in CANDIDATES {
            let l = ledger_or_die(c); // every measured point travels WITH its Lean verdict
            let config: DreggStarkConfig = create_config_with_fri_full(
                c.log_blowup,
                c.log_final_poly_len,
                IR2_FRI_MAX_LOG_ARITY,
                c.num_queries,
                c.commit_pow,
                c.query_pow,
            );

            let t0 = Instant::now();
            let proof = match prove_vm_descriptor2_with_config(
                &desc,
                &rows,
                &[],
                &mem_boundary,
                &map_heaps,
                &config,
            ) {
                Ok(p) => p,
                Err(e) => {
                    println!("{:<34} FAILED to prove: {e}", c.label);
                    continue;
                }
            };
            let prove = t0.elapsed();
            let t1 = Instant::now();
            verify_vm_descriptor2_with_config(&desc, &proof, &[], &config)
                .unwrap_or_else(|e| panic!("[{}] mocked-shape proof must verify: {e}", c.label));
            let verify = t1.elapsed();
            let bytes = postcard::to_allocvec(&proof)
                .expect("proof postcard-serializes")
                .len();

            // REJECT polarity once per shape, so the ACCEPTs above are not vacuous.
            if !tamper_checked {
                let mut tampered = proof;
                tampered.opened_values.instances[0]
                    .base_opened_values
                    .trace_local[0] +=
                    <DreggStarkConfig as p3_uni_stark::StarkGenericConfig>::Challenge::ONE;
                assert!(
                    verify_vm_descriptor2_with_config(&desc, &tampered, &[], &config).is_err(),
                    "[{}] verifier accepted a tampered opening — every ACCEPT here would be vacuous",
                    c.label
                );
                tamper_checked = true;
            }

            if c.log_blowup == IR2_FRI_LOG_BLOWUP
                && c.num_queries == IR2_FRI_NUM_QUERIES
                && c.log_final_poly_len == 0
                && c.commit_pow == 0
            {
                baseline_bytes = Some(bytes);
            }
            let vs = baseline_bytes
                .map(|b| format!("{:+.1}%", (bytes as f64 / b as f64 - 1.0) * 100.0))
                .unwrap_or_else(|| "(baseline?)".into());
            println!(
                "{:<34} {:>11} {:>11} {:>8} {:>7} | {:>7} {:>7}",
                c.label,
                bytes,
                vs,
                format!("{:.1?}", prove),
                format!("{:.1?}", verify),
                l.johnson_bits,
                l.commit_bits,
            );
        }
        assert!(
            tamper_checked,
            "[{}] no candidate proved — nothing measured on this shape",
            shape.label
        );
    }
    println!(
        "\nNOTE (read before quoting): these are MOCKED single-instance shapes. Project onto the \
         member with shape A's ratios and shape C's prover times; the flip itself is a REGEN \
         (FS epoch) staged for the Epoch-2 bundle — see HORIZONLOG (E4) for the recipe."
    );
}
