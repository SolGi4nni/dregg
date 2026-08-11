//! # The wrap conjunction, THREADED: the b-polynomial crosses rows, and the thread is what refuses.
//!
//! ## What this file is the other side of
//!
//! `MinaWrapConjunctionAir` conjoins finalize's `bCorrect`, the challenge/inverse reciprocity weld
//! and the opening residual's non-free coefficients over SHARED columns — and COMPARES `xiCorrect`
//! without forcing it (both ξ blocks are free columns there; the 32 `cb.connect`s of
//! `fold_endo_into_finalize` are what bind them, which is a consumer's constraint, not this AIR's). Its first
//! cut was ROW-LOCAL — the b-polynomial's 118 operations at both evaluation points side by side —
//! and measured **22 184 columns, 30 607 constraints, a 24 MB artifact**, ten times the largest
//! descriptor in the tree. `EmitByName.lean` WITHHELD the routing row rather than check in that
//! shape.
//!
//! `dregg-mina-wrap-conjunction::v1` is the layout that answers it. Same conjunction, same sound
//! cores, same recursion bind — plus **448 `.transition` window legs** carrying the fold's four
//! registers (`sq` and `fld`, at ζ and at ζω) and the ten global blocks into the next row. The
//! b-polynomial's 15 rounds are 15 ROWS, so:
//!
//! * `trace_width` is **2 536 at every round count** (`threaded_conj_width_is_flat`), where the
//!   row-local layout cost 1 326 fresh columns per round;
//! * the descriptor is **4 317 constraints** (4 157 of arithmetic and thread, plus the 160
//!   `pi_binding`s of the 2026-08-06 public surface), ~7× smaller than the 30 607 that were
//!   withheld.
//!
//! ⚑ **AND THE ROW COUNT IS THE ROUND COUNT PLUS ONE.** `.transition` fires on every row but the
//! last, so a 16-row trace has exactly 15 transitions — Mina's 15 IPA rounds — and one terminal row
//! that READS the finished register. The deployed prover requires a power-of-two height and
//! `15 + 1 = 16`. No padding convention, no spare rows.
//!
//! ## ⚑ THE FIXTURE IS THE REAL BLOCK'S OPENING ARGUMENT
//!
//! ζ, ζω, ξ and the evalscale `r` are `MinaRealBlockGate`'s extracted Wrap-side scalars; the 15 IPA
//! challenges, their inverses, `c`, `z1`, `z2`, `cip` and the claimed `b0` are
//! `MinaWrapOpeningGate`'s, DERIVED there from the block's own sponge. The honest trace's terminal
//! row therefore reproduces `MinaWrapOpeningGate.B0` — the same number
//! `b0_is_the_b_polynomial : bPoly CHAL ζ + r · bPoly CHAL ζω = B0` proves in Lean — which is
//! asserted below (`the_honest_trace_claims_the_real_blocks_b0`).
//!
//! ## ⚑ THE FALSIFIER, AND WHY IT ISOLATES THE GATE UNDER TEST
//!
//! This campaign has twice shipped a falsifier that passed for the wrong reason — one moved a zero
//! into a zero, another was refused by a range lookup rather than by the gate being tested. So the
//! forged fixture here is built to leave nothing else available to refuse it:
//!
//! * it is **sixteen independently HONEST rows**. Every row's own arithmetic holds: every sound
//!   multiply, every add/sub, every reciprocity comparison, the `.first` seed pins AND the `.last`
//!   `bCorrect` comparison (`b0` is set to what the forged fold actually produces);
//! * **every cell is a real limb**, inside the declared 8-bit / 16-bit widths
//!   (`the_forgery_is_inside_the_limb_width`), so no range lookup can be the refusal;
//! * **5 156 cells move** between the honest and forged fixtures
//!   (`the_falsifier_actually_moves_values`);
//! * the ONLY thing wrong with it is that row 14's fold registers are RE-SEEDED to `(ζ, 1)` /
//!   `(ζω, 1)` instead of continuing row 13's.
//!
//! That is a real forgery, not a scribble: it claims `b0` for a ONE-factor b-polynomial instead of
//! the 15-factor one, and `the_forgery_claims_a_different_b0` says the two numbers differ. Sixteen
//! independently honest rows is **exactly what a fold looks like when the register is re-pinned
//! instead of threaded**, which is why the refusal below is the load-bearing statement of the whole
//! layout.
//!
//! ⚠ **Run in RELEASE.** The algebraic refusals are debug-assert panics in debug and clean `Err`s in
//! release:
//!
//! ```text
//! cargo test -p dregg-circuit --release --test mina_wrap_conjunction_thread_proves -- --nocapture
//! ```
//!
//! ## Provenance
//!
//! Descriptors: `metatheory/EmitByName.lean` rows `mina-wrap-conjunction.json` /
//! `mina-wrap-conjunction-unthreaded.json` → `MinaWrapConjunctionAir.{conjunctionDesc,
//! conjunctionUnthreadedDesc}`, each `EffectLower.lowerAir` of a Lean-authored `EffectAir`. Traces:
//! `metatheory/EmitMinaWrapConjunction.lean` (`trace` / `forged`), Lean-generated from
//! `MinaWrapConjunctionAir.conjunctionRow` over the real block's transcript. Rust fills cells; it
//! authors nothing.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

const DESC_JSON: &str = include_str!("../descriptors/by-name/mina-wrap-conjunction.json");
const UNTHREADED_JSON: &str =
    include_str!("../descriptors/by-name/mina-wrap-conjunction-unthreaded.json");

const TRACE: &str = include_str!("fixtures/mina-wrap-conjunction-trace.txt");
const FORGED: &str = include_str!("fixtures/mina-wrap-conjunction-forged-trace.txt");
/// ⚑ The five published blocks, rendered by `EmitMinaWrapConjunction.lean pis` from the BLOCK'S
/// SCALARS — not scraped off the trace, which would be a pin against its own definition.
const PIS: &str = include_str!("fixtures/mina-wrap-conjunction-pis.txt");
/// …and the forged fold's, carrying the `b0` the forged fold actually computes, so the falsifier
/// cannot be refused by a PI mismatch it could have avoided.
const FORGED_PIS: &str = include_str!("fixtures/mina-wrap-conjunction-forged-pis.txt");

const WIDTH: usize = 2536;
/// 15 IPA round rows plus the terminal read row.
const ROWS: usize = 16;
const NCHAL: usize = 15;
/// The threaded descriptor's constraints; the twin is this minus the 448 window legs.
/// ⚑ 4 317, not 4 157: `2026-08-06` gave the conjunction a PUBLIC SURFACE — 160 `pi_binding`
/// constraints pinning ξ, ζ, ζω, `r` and the claimed `b0`, so the claim has a subject a consumer
/// can name. The width did not move (`the_public_surface_costs_no_column`).
const CONSTRAINTS: usize = 4317;
/// Five 32-limb blocks (`MinaWrapConjunctionAir.CJ_PI_COUNT`).
const PI_COUNT: usize = 160;
/// PI offsets of the five published blocks.
const PI_XI: usize = 0;
const PI_ZETA: usize = SK;
const PI_ZETAW: usize = 2 * SK;
const PI_R: usize = 3 * SK;
const PI_B0: usize = 4 * SK;
const THREAD_LEGS: usize = 448;
/// Limbs per Pasta field element in the sound encoding.
const SK: usize = 32;
/// 18 input blocks: 10 global, 2 constant, 4 register, 2 per-row.
const NIN: usize = 18;
const SCRATCH: usize = SK * NIN;

/// The four register blocks on the input side.
const SQ_IN: [usize; 2] = [SK * 12, SK * 13];
const FLD_IN: [usize; 2] = [SK * 14, SK * 15];
/// …and the four computed outputs the thread carries into them.
const SQ_OUT: [usize; 2] = [SCRATCH, SCRATCH + SK];
const FLD_OUT: [usize; 2] = [SCRATCH + SK * 6, SCRATCH + SK * 7];

/// ζ and ζω — the seed pins' targets.
const PT: [usize; 2] = [SK * 7, SK * 8];
/// The claimed `b0` block, and the terminal row's computed `bActualOf`.
const B_CL: usize = SK * 2;
const B_ACT: usize = SCRATCH + SK * 12;
/// The pinned `1` block.
const ONE: usize = SK * 10;

/// `MinaWrapOpeningGate.B0`, the real block's claimed `b0`, base-`2^8` limbs least-significant
/// first. This is the number `b0_is_the_b_polynomial` proves is
/// `bPoly CHAL ζ + r · bPoly CHAL ζω` — so it is the block's, not this test's.
/// `MinaRealBlockGate.VV` — block 539508's polyscale ξ, extracted from the block's own proof.
const XI_DECIMAL: &str =
    "8288233988205559029449525580974252420889527181759196726389788710191542809415";
/// `MinaRealBlockGate.ZETA` — the first evaluation point, endo-mapped.
const ZETA_DECIMAL: &str =
    "5882778464885448390370243325569768165017976480253711597216088892712827726750";
/// `MinaRealBlockGate.UU` — the evalscale `r`.
const R_DECIMAL: &str =
    "6201396350626737261036432388107935815953346991927125598065137346871745847675";
const B0_DECIMAL: &str =
    "8959513835325565174995450957597499793792733131117505895288870852340268010913";

fn descriptor(json: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2(json).expect("the STRICT deployed checker parses the threaded conjunction")
}

fn trace(text: &str) -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(rows.len(), ROWS);
    assert!(rows.iter().all(|r| r.len() == WIDTH));
    rows
}

/// The Lean-emitted public-input vector.
fn pis(text: &str) -> Vec<BabyBear> {
    let v: Vec<BabyBear> = text
        .split_whitespace()
        .map(|w| BabyBear::new(w.parse::<u64>().expect("PI limb is a decimal") as u32))
        .collect();
    assert_eq!(v.len(), PI_COUNT, "the PI vector is five 32-limb blocks");
    v
}

/// …the same vector as raw decimals, for the assertions about the FIXTURE.
fn pi_cells(text: &str) -> Vec<u64> {
    text.split_whitespace()
        .map(|w| w.parse::<u64>().expect("PI limb is a decimal"))
        .collect()
}

/// The raw decimal cells, for the assertions about the FIXTURE (not about the field).
fn cells(text: &str) -> Vec<Vec<u64>> {
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| t.parse::<u64>().expect("cell is a u64 decimal"))
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Recompose a 32-limb base-`2^8` block into a decimal string, so a fixture claim can be checked
/// against the block's own published scalar rather than against another fixture.
fn block_decimal(row: &[u64], base: usize) -> String {
    // little-endian base-256 digits -> decimal, by schoolbook multiply-add on decimal digits.
    let mut acc: Vec<u32> = vec![0]; // little-endian decimal digits
    for i in (0..SK).rev() {
        // acc = acc * 256 + limb
        let mut carry: u32 = row[base + i] as u32;
        for d in acc.iter_mut() {
            let v = *d * 256 + carry;
            *d = v % 10;
            carry = v / 10;
        }
        while carry > 0 {
            acc.push(carry % 10);
            carry /= 10;
        }
    }
    while acc.len() > 1 && *acc.last().unwrap() == 0 {
        acc.pop();
    }
    acc.iter()
        .rev()
        .map(|d| char::from(b'0' + *d as u8))
        .collect()
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// The shape, measured off the parsed descriptors.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE WIDTH IS FLAT AND THE ARTIFACT COLLAPSED.** The withheld row-local layout declared
/// 22 184 columns and 30 607 constraints. This declares 2 536 and 4 317 — and the 2 536 does not
/// depend on the round count at all, which is the property a wider row can never have.
#[test]
fn the_threaded_conjunction_is_flat_and_small() {
    let d = descriptor(DESC_JSON);
    assert_eq!(d.name, "dregg-mina-wrap-conjunction::v1");
    assert_eq!(d.trace_width, WIDTH, "2 536 at EVERY round count");
    assert_eq!(d.constraints.len(), CONSTRAINTS);
    assert_eq!(
        d.tables.len(),
        4,
        "main + range_w8 + range_w16 + range_w1 — the same union the sound cores declare"
    );
    // the layout that was refused, as the two numbers it was refused over
    assert!(
        8 * d.trace_width < 22184,
        "the row-local layout was more than 8x wider"
    );
    assert!(
        7 * d.constraints.len() < 30607 && 30607 < 8 * d.constraints.len(),
        "and carried ~7.4x the constraints"
    );
}

/// ⚑ **EVERY THREAD GATE IS `on_transition`, AND THERE ARE 448 OF THEM.**
///
/// The selector is the whole content. Under `.all` the last row's `next` is the WRAP row, so an
/// every-row thread says something different exactly where padding hides; a `.transition → .all`
/// re-scope is byte-identical algebra that accepts strictly more. It is invisible to a constraint
/// count and visible here.
#[test]
fn every_thread_gate_is_scoped_to_the_transition() {
    let d = descriptor(DESC_JSON);
    let windows = d
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(
        windows, THREAD_LEGS,
        "four registers + ten global blocks, 32 limbs each"
    );
    let on_transition = d
        .constraints
        .iter()
        .filter(|c| match c {
            VmConstraint2::WindowGate(g) => g.on_transition,
            _ => false,
        })
        .count();
    assert_eq!(
        on_transition, THREAD_LEGS,
        "all 448 are transition-scoped; an every-row thread would accept strictly more"
    );
}

/// ⚑ **THE SEED AND THE READ ARE BOUNDARY GATES, AT OPPOSITE ENDS.** 128 `when_first_row` bodies
/// pin the fold's four registers (`sq` to the named ζ/ζω columns, `fld` to the pinned `1`), and 32
/// `when_last_row` bodies compare the finished `bActualOf` against the claimed slot. Without the
/// first-row pins the theorem would only say "the chain from whatever row 0 held"; without the
/// last-row scope the comparison would be false on every intermediate row.
#[test]
fn the_seed_pins_and_the_read_are_at_opposite_ends() {
    let d = descriptor(DESC_JSON);
    let count = |want: VmRow| {
        d.constraints
            .iter()
            .filter(|c| {
                matches!(
                    c,
                    VmConstraint2::Base(VmConstraint::Boundary { row, .. }) if *row == want
                )
            })
            .count()
    };
    assert_eq!(count(VmRow::First), 4 * SK, "two sq seeds + two fld seeds");
    assert_eq!(count(VmRow::Last), SK, "the bCorrect comparison, once");
}

/// ⚑ **ONE RECURSION SEAM, AND IT IS NOT THE DECLARATIVE SHAPE.** Eight bound lanes, all of them
/// cells the row's own gates forced.
#[test]
fn the_seam_is_pinned_and_eight_lanes_wide() {
    let d = descriptor(DESC_JSON);
    let binds: Vec<_> = d
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::ProofBind(b) => Some(b),
            _ => None,
        })
        .collect();
    assert_eq!(binds.len(), 1);
    assert_eq!(binds[0].commit.len(), 8);
    assert_eq!(binds[0].vk.len(), 8);
    assert!(
        binds[0].bound.lanes().is_some(),
        "the commitment half is pinned to row expressions"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// The fixture, before the prover sees it — so a green polarity below cannot be green for a reason
// the fixture quietly supplied.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE HONEST TRACE IS ACTUALLY THREADED, AND THE FOLD ACTUALLY WALKS.**
///
/// Sixteen copies of one row would satisfy the thread only at a fixed point of the squaring map.
/// This asserts every register genuinely advances — 16 distinct powers and 16 distinct running
/// products at each evaluation point — so the honest polarity is not passing on a degenerate
/// witness, and the 448 window gates are not vacuous.
#[test]
fn the_honest_trace_threads_and_the_fold_walks() {
    let t = cells(TRACE);
    for r in 0..ROWS - 1 {
        for e in 0..2 {
            for i in 0..SK {
                assert_eq!(
                    t[r + 1][SQ_IN[e] + i],
                    t[r][SQ_OUT[e] + i],
                    "row {r} sq[{e}] limb {i}"
                );
                assert_eq!(
                    t[r + 1][FLD_IN[e] + i],
                    t[r][FLD_OUT[e] + i],
                    "row {r} fld[{e}] limb {i}"
                );
            }
        }
    }
    for e in 0..2 {
        for base in [SQ_IN[e], FLD_IN[e]] {
            let seen: std::collections::HashSet<Vec<u64>> =
                (0..ROWS).map(|r| t[r][base..base + SK].to_vec()).collect();
            assert_eq!(
                seen.len(),
                ROWS,
                "sixteen DISTINCT register values at block {base}; a fixed-point fixture would be \
                 1 and would make the thread gates vacuous"
            );
        }
    }
}

/// ⚑ **THE SEED PINS AND THE GLOBAL HOLDS ARE REAL IN THE FIXTURE.** Row 0's squaring registers are
/// the named ζ/ζω columns and its product registers are the pinned `1`; the ten global blocks do not
/// move down the trace.
#[test]
fn the_honest_trace_seeds_and_holds() {
    let t = cells(TRACE);
    for e in 0..2 {
        for i in 0..SK {
            assert_eq!(t[0][SQ_IN[e] + i], t[0][PT[e] + i], "seed sq[{e}] limb {i}");
            assert_eq!(t[0][FLD_IN[e] + i], t[0][ONE + i], "seed fld[{e}] limb {i}");
        }
    }
    // the ten global blocks, by base column
    for base in [
        0,
        SK,
        SK * 2,
        SK * 3,
        SK * 4,
        SK * 5,
        SK * 6,
        SK * 7,
        SK * 8,
        SK * 9,
    ] {
        for r in 1..ROWS {
            assert_eq!(
                t[r][base..base + SK],
                t[0][base..base + SK],
                "global block {base} moved at row {r}"
            );
        }
    }
}

/// ⚑ **AND THE HONEST TRACE'S CLAIM IS THE REAL BLOCK'S `b0`.**
///
/// The terminal row's `bActualOf` recomposes to `MinaWrapOpeningGate.B0` — the number Lean proves is
/// `bPoly CHAL ζ + r · bPoly CHAL ζω`. So the threaded fold computes the b-polynomial of the actual
/// Mina transcript, and the fixture is that transcript's opening argument rather than an invented
/// one. A wrong row order, a wrong challenge index or a wrong squaring direction would land
/// somewhere else.
#[test]
fn the_honest_trace_claims_the_real_blocks_b0() {
    let t = cells(TRACE);
    assert_eq!(block_decimal(&t[NCHAL], B_ACT), B0_DECIMAL);
    assert_eq!(block_decimal(&t[NCHAL], B_CL), B0_DECIMAL);
}

/// ⚑ **THE SEAM'S COMMITMENT IS THE ROW'S OWN FORCED CELLS, AND THEY ARE NOT ZERO.**
///
/// The deployed AIR asserts `guard · (commit − bound) = 0`, so a fixture that left the commitment
/// block zero would only prove if the coefficients were zero too — which is how a recursion seam
/// quietly becomes vacuous. The honest witness carries limb 0 of `UBC`, `−z1`, `−z2`, `c·cip`,
/// `z1·b0`, `c·chalinv`, `c·chal` and `bActualOf` in the commitment lanes, and this asserts they are
/// live values rather than a satisfying nothing.
#[test]
fn the_seam_commits_to_live_coefficients() {
    let t = cells(TRACE);
    const COMMIT: usize = SCRATCH + SK * 19;
    let bound_bases = [
        SCRATCH + SK * 15, // UBC
        SCRATCH + SK * 16, // NEG_Z1
        SCRATCH + SK * 17, // NEG_Z2
        SCRATCH + SK * 13, // CCIP
        SCRATCH + SK * 14, // Z1B0
        SCRATCH + SK * 9,  // LC
        SCRATCH + SK * 10, // RC
        B_ACT,
    ];
    for r in 0..ROWS {
        for (lane, base) in bound_bases.iter().enumerate() {
            assert_eq!(
                t[r][COMMIT + lane],
                t[r][*base],
                "row {r} seam lane {lane} is not the coefficient cell it binds"
            );
        }
        let live = (0..8).filter(|&l| t[r][COMMIT + l] != 0).count();
        assert!(
            live >= 6,
            "row {r} commits to {live} non-zero lanes; an all-zero commitment would satisfy the \
             seam while binding nothing"
        );
    }
}

/// ⚑ **THE FALSIFIER ACTUALLY MOVES VALUES** — the check this campaign paid for twice.
/// A tamper that moved a zero into a zero once had `decide` prove it was not a tamper.
#[test]
fn the_falsifier_actually_moves_values() {
    let h = cells(TRACE);
    let f = cells(FORGED);
    assert_eq!(h.len(), f.len());
    let moved: usize = (0..ROWS)
        .map(|r| (0..WIDTH).filter(|&c| h[r][c] != f[r][c]).count())
        .sum();
    assert!(
        moved > 5000,
        "the forgery must MOVE cells, not relabel them; moved = {moved}"
    );
}

/// ⚑ **AND IT CLAIMS A DIFFERENT `b0`** — so the forgery is a real claim about the b-polynomial and
/// not a cosmetic edit. The forged fold restarts at row 14, so what it claims is the ONE-factor
/// b-polynomial where the honest trace claims the fifteen-factor one.
#[test]
fn the_forgery_claims_a_different_b0() {
    let h = cells(TRACE);
    let f = cells(FORGED);
    assert_eq!(block_decimal(&h[NCHAL], B_CL), B0_DECIMAL);
    assert_ne!(
        block_decimal(&f[NCHAL], B_CL),
        B0_DECIMAL,
        "a forgery that claimed the same b0 would prove nothing"
    );
}

/// ⚑ **AND THE FORGERY IS INSIDE THE LIMB WIDTH** — so a range lookup CANNOT be what refuses it.
///
/// This is the second wrong-reason failure this campaign hit: a falsifier refused by a range check
/// rather than by the gate under test passes while proving nothing about that gate. Every cell of
/// the forged trace is a genuine limb or a genuine carry.
#[test]
fn the_forgery_is_inside_the_limb_width() {
    let f = cells(FORGED);
    for r in 0..ROWS {
        for c in 0..SCRATCH {
            assert!(
                f[r][c] < 256,
                "row {r} input limb {c} = {} is outside the declared 8-bit width; a range lookup \
                 would refuse this trace and the thread gate would never be reached",
                f[r][c]
            );
        }
        for c in 0..WIDTH {
            assert!(
                f[r][c] < 65536,
                "row {r} cell {c} = {} is outside the widest declared range table",
                f[r][c]
            );
        }
    }
}

/// ⚑ **AND THE FORGED TRACE BREAKS ONLY THE SEAM.** Its seed pins hold, its `.last` comparison
/// holds (the claimed `b0` is what the forged fold actually produced), its globals are held — and
/// exactly ONE of the fifteen transitions fails to carry.
#[test]
fn the_forged_trace_breaks_only_one_transition() {
    let f = cells(FORGED);
    // the `.first` seed pins still hold
    for e in 0..2 {
        for i in 0..SK {
            assert_eq!(f[0][SQ_IN[e] + i], f[0][PT[e] + i]);
            assert_eq!(f[0][FLD_IN[e] + i], f[0][ONE + i]);
        }
    }
    // the `.last` bCorrect comparison still holds
    for i in 0..SK {
        assert_eq!(
            f[NCHAL][B_ACT + i],
            f[NCHAL][B_CL + i],
            "the forged claim matches the forged fold, so `bCorrect` cannot be the refusal"
        );
    }
    let breaks: Vec<usize> = (0..ROWS - 1)
        .filter(|&r| {
            (0..2).any(|e| {
                (0..SK).any(|i| {
                    f[r + 1][SQ_IN[e] + i] != f[r][SQ_OUT[e] + i]
                        || f[r + 1][FLD_IN[e] + i] != f[r][FLD_OUT[e] + i]
                })
            })
        })
        .collect();
    assert_eq!(
        breaks,
        vec![13],
        "exactly one broken transition — the 13 -> 14 seam, where the fold restarts"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// BOTH POLARITIES.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE PUBLIC SURFACE NAMES THE REAL BLOCK, AND THE SOURCE IS NOT THIS FIXTURE.**
///
/// `dregg-mina-wrap-conjunction::v1` publishes five 32-limb blocks. Four of them have an
/// INDEPENDENT decimal in the tree — `MinaRealBlockGate.VV` (the polyscale ξ), `.ZETA`, `.UU` (the
/// evalscale `r`) and `MinaWrapOpeningGate.B0` — extracted from Mina devnet block 539508 and used
/// by no other part of this file. Asserting the emitted PI vector against them is a gate with two
/// sources; asserting it against the trace it pins would be a pin against its own definition.
///
/// ⚠ The fifth, ζω, is `ZETA * OMEGA` and has no standalone literal; what is asserted here is that
/// it is a distinct in-range block, and its value is Lean's (`MinaRealBlockGate.ZETAW`).
#[test]
fn the_published_surface_is_the_real_blocks_deferred_values() {
    let p = pi_cells(PIS);
    assert_eq!(p.len(), PI_COUNT);
    assert_eq!(
        block_decimal(&p, PI_XI),
        XI_DECIMAL,
        "PI[0..32] is the block's polyscale"
    );
    assert_eq!(
        block_decimal(&p, PI_ZETA),
        ZETA_DECIMAL,
        "PI[32..64] is the block's zeta"
    );
    assert_eq!(
        block_decimal(&p, PI_R),
        R_DECIMAL,
        "PI[96..128] is the block's evalscale"
    );
    assert_eq!(
        block_decimal(&p, PI_B0),
        B0_DECIMAL,
        "PI[128..160] is the b0 `b0_is_the_b_polynomial` proves is bPoly(zeta) + r*bPoly(zeta*w)"
    );
    assert_ne!(block_decimal(&p, PI_ZETAW), ZETA_DECIMAL);
    assert!(p.iter().all(|&l| l < 256), "every published limb is a byte");
}

/// ⚑ **AND THE PUBLISHED `b0` IS THE ONE THE TRACE'S OWN FOLD LANDS ON.** The prover's
/// `pi_binding` check is what enforces this; this is the assertion that the FIXTURE would not have
/// passed for a trivial reason (e.g. an all-zero PI vector, which no `pi_binding` would refuse if
/// row 0 were also zero).
#[test]
fn the_published_b0_is_the_folds_terminal_value() {
    let t = cells(TRACE);
    let p = pi_cells(PIS);
    assert_eq!(block_decimal(&p, PI_B0), block_decimal(&t[NCHAL], B_ACT));
    // …and the FORGED vector publishes a DIFFERENT b0 — so the falsifier below is refused by the
    // thread, not by a public input it failed to update.
    let f = pi_cells(FORGED_PIS);
    assert_ne!(block_decimal(&f, PI_B0), B0_DECIMAL);
    assert_eq!(
        block_decimal(&f, PI_XI),
        XI_DECIMAL,
        "and it names the same block"
    );
}

/// ⚑ **POLARITY 1 — THE THREADED CONJUNCTION PROVES.** Fifteen rounds of the b-polynomial at both
/// evaluation points, the reciprocity weld on every round row, the opening's non-free coefficients
/// and the recursion seam — the registers carried across every seam by the emitted window gates,
/// proved and verified by the deployed `prove_vm_descriptor2` / `verify_vm_descriptor2`.
#[test]
fn the_threaded_conjunction_proves_and_verifies() {
    let d = descriptor(DESC_JSON);
    let t = trace(TRACE);
    let p = pis(PIS);
    let proof = prove_vm_descriptor2(&d, &t, &p, &MemBoundaryWitness::default(), &[])
        .unwrap_or_else(|e| panic!("the honest threaded trace must prove: {e:?}"));
    verify_vm_descriptor2(&d, &proof, &p)
        .unwrap_or_else(|e| panic!("the honest threaded proof must verify: {e:?}"));
}

/// ⚑ **POLARITY 2 — AND THE THREAD IS WHAT REFUSES THE RESTARTED FOLD.**
///
/// The refusing gate, named: a `VmConstraint2::WindowGate { on_transition: true }` whose body is
/// `nxt(FLD_IN[e] + i) - loc(FLD_OUT[e] + i)`, emitted by `MinaWrapConjunctionAir.carryLeg`.
/// Nothing else in the descriptor can refuse this trace — every row's arithmetic holds, the seed
/// pins hold, the `bCorrect` comparison holds (`the_forged_trace_breaks_only_one_transition`) and
/// every cell is a legal limb (`the_forgery_is_inside_the_limb_width`).
///
/// This is the whole distinction between a threaded fold and a re-pinned one, as a refusal.
#[test]
fn the_restarted_fold_is_refused_by_the_thread() {
    let d = descriptor(DESC_JSON);
    let t = trace(FORGED);
    let r = prove_vm_descriptor2(
        &d,
        &t,
        &pis(FORGED_PIS),
        &MemBoundaryWitness::default(),
        &[],
    );
    assert!(
        r.is_err(),
        "sixteen independently honest rows whose b-polynomial register does NOT chain must be \
         refused — and the only constraint that can refuse them is a transition window gate"
    );
}

/// ⚑ **THE SAME TRACE WITHOUT THE THREAD IS ACCEPTED** — which is what makes the refusal above a
/// statement about the 448 window gates rather than about the fixture.
///
/// `dregg-mina-wrap-conjunction-unthreaded::v1` is the SAME Lean `EffectAir` minus the thread
/// (`MinaWrapConjunctionAir.the_twin_is_the_thread_removed` proves the two differ by exactly the
/// 448 legs and in no other selector). It is emitted, not assembled here: filtering constraints out
/// of a parsed descriptor in Rust would be Rust authoring AIR.
#[test]
fn without_the_thread_the_forged_trace_proves() {
    let unthreaded = descriptor(UNTHREADED_JSON);
    assert_eq!(
        unthreaded.name,
        "dregg-mina-wrap-conjunction-unthreaded::v1"
    );
    assert_eq!(unthreaded.trace_width, WIDTH);
    assert_eq!(
        unthreaded.constraints.len(),
        CONSTRAINTS - THREAD_LEGS,
        "the twin IS the threaded descriptor minus the 448 window gates"
    );
    assert_eq!(
        unthreaded
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count(),
        0
    );
    let t = trace(FORGED);
    let p = pis(FORGED_PIS);
    let proof = prove_vm_descriptor2(&unthreaded, &t, &p, &MemBoundaryWitness::default(), &[])
        .expect(
            "every row of the forged trace is an honest row of the unthreaded descriptor — so it \
             accepts, and the refusal in the test above is the thread's doing",
        );
    verify_vm_descriptor2(&unthreaded, &proof, &p).expect("and the unthreaded proof verifies");
}
