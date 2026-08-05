//! # The THREADED sound Pasta curve row: the accumulator crosses rows, and the thread refuses.
//!
//! ## What this file is the other side of
//!
//! `PastaCurveSound.sound_ladder_does_not_fit_a_row` priced the ROW-LOCAL sound ladder:
//! `PastaMsmAir.ladderGatesFrom_counts` proves the ladder puts `884·n` fresh columns in ONE row, so
//! on the sound gate a 128-step GLV joint ladder is **731 136 columns in a single row** — against
//! the deployed `pasta_derive_prove` measuring 2 131. That is a layout wall, and the same wall is
//! why `PastaMsmAir.minaOpeningCheckDesc` (the bulletproof opening check) **would be refused by the
//! deployed prover**: it declares `trace_width = 442` while its constraints address columns near
//! `10^7`, and `descriptor_ir2.rs` rejects `column >= trace_width`.
//!
//! `dregg-pasta-{pallas,vesta}-rcb-thread::v1` is the layout that answers it. Same RCB Algorithm 7,
//! same 33 SSA ops, same `SoundCore` bridge, same 4 476 constraints — plus **96 `.transition`
//! window gates** carrying the accumulator `(X3, Y3, Z3)` of row `r` into the accumulator input of
//! row `r+1`, one per limb of the three projective coordinates. The width is **3 048 at every
//! ladder depth**, because the depth is rows.
//!
//! ## ⚑ THE FALSIFIER, AND WHY IT ISOLATES THE GATE UNDER TEST
//!
//! This campaign has twice shipped a falsifier that passed for the wrong reason — one moved a zero
//! into a zero, another was refused by a range lookup rather than by the gate being tested. So the
//! forged fixture here is built to leave nothing else available to refuse it:
//!
//! * it is **eight independently HONEST rows**. The last row is `rcbSoundRow` at `(G, G)` —
//!   every one of its own 4 476 constraints holds, every coefficient gate is satisfied;
//! * **every cell is a real limb**, well inside the declared 8-bit / 16-bit widths
//!   (`the_forgery_is_inside_the_limb_width` asserts it), so no range lookup can be the refusal;
//! * **2 226 cells move** between the honest and forged fixtures
//!   (`the_falsifier_actually_moves_values`), so it is not a tamper that tampers with nothing;
//! * the ONLY thing wrong with it is that row 7's accumulator input is `G` where row 6's output is
//!   `8G`.
//!
//! Eight independently honest rows is **exactly what a ladder looks like when the accumulator is
//! re-pinned instead of threaded**. So the refusal below is the load-bearing statement of the whole
//! layout: the `.transition` window gate is what makes a chain of rows a chain.
//!
//! ⚠ **Run in RELEASE.** The algebraic refusals are debug-assert panics in debug and clean `Err`s
//! in release:
//!
//! ```text
//! cargo test -p dregg-circuit --release --test pasta_rcb_thread_proves -- --nocapture
//! ```
//!
//! ## Provenance
//!
//! Descriptors: `metatheory/EmitByName.lean` rows `pasta-pallas-rcb-thread.json` /
//! `pasta-vesta-rcb-thread.json` → `PastaLadderThread.{pallas,vesta}ThreadDesc`, each
//! `EffectLower.lowerAir` of a Lean-authored `EffectAir`. Traces: `metatheory/EmitPastaLadderThread
//! .lean` (`pallastrace`/`vestatrace`, and `pallasforged`/`vestaforged`), Lean-generated from
//! `PastaCurveSound.rcbSoundRow` chained by `PastaCurveComplete.rcbAddM`. Rust fills cells; it
//! authors nothing.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};

const PALLAS_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-pallas-rcb-thread.json");
const VESTA_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-vesta-rcb-thread.json");

const PALLAS_TRACE: &str = include_str!("fixtures/pasta-pallas-rcb-thread-trace.txt");
const VESTA_TRACE: &str = include_str!("fixtures/pasta-vesta-rcb-thread-trace.txt");
const PALLAS_FORGED: &str = include_str!("fixtures/pasta-pallas-rcb-thread-forged-trace.txt");
const VESTA_FORGED: &str = include_str!("fixtures/pasta-vesta-rcb-thread-forged-trace.txt");

const WIDTH: usize = 3048;
const ROWS: usize = 8;
/// 4 476 row-local constraints + 96 `.transition` window gates.
const CONSTRAINTS: usize = 4476 + 96;
/// Limbs per Pasta field element in the sound encoding.
const SK: usize = 32;
/// The gadget's scratch begins after the six input blocks.
const IN_BASE: usize = 6 * SK;

/// The accumulator's three input blocks.
const ACC_X: usize = 0;
const ACC_Y: usize = SK;
const ACC_Z: usize = 2 * SK;

/// `X3` is SSA intermediate 26 (`X3g`), `Y3` is 29 (`Y3f`), `Z3` is 32 (`Z3c`).
const OUT_X: usize = IN_BASE + SK * 26;
const OUT_Y: usize = IN_BASE + SK * 29;
const OUT_Z: usize = IN_BASE + SK * 32;

fn descriptor(json: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2(json).expect("the STRICT deployed checker parses the threaded row")
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

// ────────────────────────────────────────────────────────────────────────────────────────────────
// The shape, measured off the parsed descriptors.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE WIDTH IS FLAT AND THE THREAD IS 96 GATES.** The threaded row costs exactly the
/// standalone sound row plus one window gate per threaded limb — and its width does not depend on
/// the ladder's depth at all, which is the property the row-local layout cannot have.
#[test]
fn the_threaded_row_is_the_sound_row_plus_96_transition_gates() {
    for (name, json) in [
        ("dregg-pasta-pallas-rcb-thread::v1", PALLAS_DESC_JSON),
        ("dregg-pasta-vesta-rcb-thread::v1", VESTA_DESC_JSON),
    ] {
        let d = descriptor(json);
        assert_eq!(d.name, name);
        assert_eq!(d.trace_width, WIDTH, "3 048 at EVERY ladder depth");
        assert_eq!(
            d.constraints.len(),
            CONSTRAINTS,
            "4 476 row-local + 96 accumulator-thread window gates"
        );
        assert_eq!(
            d.tables.len(),
            4,
            "main + range_w8 + range_w16 + range_w1 — the same union the standalone sound row \
             declares, and nothing new"
        );
    }
}

/// ⚑ **EVERY THREAD GATE IS `on_transition`, AND THERE ARE 96 OF THEM.**
///
/// The selector is the whole content. Under `.all` the last row's `next` is the WRAP row, so an
/// every-row thread says something different exactly where padding hides; a `.transition → .all`
/// re-scope is byte-identical algebra that accepts strictly more. It is invisible to a constraint
/// count and visible here.
#[test]
fn every_thread_gate_is_scoped_to_the_transition() {
    for json in [PALLAS_DESC_JSON, VESTA_DESC_JSON] {
        let d = descriptor(json);
        let windows = d
            .constraints
            .iter()
            .filter(|c| {
                matches!(
                    c,
                    dregg_circuit::descriptor_ir2::VmConstraint2::WindowGate(_)
                )
            })
            .count();
        assert_eq!(windows, 96, "three coordinates x 32 limbs");
        let on_transition = d
            .constraints
            .iter()
            .filter(|c| match c {
                dregg_circuit::descriptor_ir2::VmConstraint2::WindowGate(g) => g.on_transition,
                _ => false,
            })
            .count();
        assert_eq!(
            on_transition, 96,
            "all 96 are transition-scoped; an every-row thread would accept strictly more"
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// The fixture, before the prover sees it — so a green polarity below cannot be green for a reason
// the fixture quietly supplied.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE HONEST TRACE IS ACTUALLY THREADED, AND IS NOT A FIXED POINT.**
///
/// `EmitPastaCurveSound`'s fixture repeats ONE row eight times, which is legal there because the
/// standalone row's constraints are row-local. Eight copies of one row would satisfy the thread
/// only at a fixed point of the group law. This asserts the accumulator genuinely walks — the
/// trace is `2G, 3G, … 9G` — so the honest polarity is not passing on a degenerate witness.
#[test]
fn the_honest_trace_threads_and_walks() {
    for text in [PALLAS_TRACE, VESTA_TRACE] {
        let t = cells(text);
        for r in 0..ROWS - 1 {
            for i in 0..SK {
                assert_eq!(t[r + 1][ACC_X + i], t[r][OUT_X + i], "row {r} X limb {i}");
                assert_eq!(t[r + 1][ACC_Y + i], t[r][OUT_Y + i], "row {r} Y limb {i}");
                assert_eq!(t[r + 1][ACC_Z + i], t[r][OUT_Z + i], "row {r} Z limb {i}");
            }
        }
        let accs: std::collections::HashSet<Vec<u64>> = (0..ROWS)
            .map(|r| t[r][ACC_X..ACC_X + SK].to_vec())
            .collect();
        assert_eq!(
            accs.len(),
            ROWS,
            "eight DISTINCT accumulators; a fixed-point fixture would be 1 and would make the \
             thread gates vacuous"
        );
    }
}

/// ⚑ **THE FALSIFIER ACTUALLY MOVES VALUES** — the check this campaign paid for twice.
/// A tamper that moved a zero into a zero once had `decide` prove it was not a tamper.
#[test]
fn the_falsifier_actually_moves_values() {
    for (honest, forged) in [(PALLAS_TRACE, PALLAS_FORGED), (VESTA_TRACE, VESTA_FORGED)] {
        let h = cells(honest);
        let f = cells(forged);
        assert_eq!(h.len(), f.len());
        let moved: usize = (0..ROWS)
            .map(|r| (0..WIDTH).filter(|&c| h[r][c] != f[r][c]).count())
            .sum();
        assert!(
            moved > 2000,
            "the forgery must MOVE cells, not relabel them; moved = {moved}"
        );
        let rows_differing: Vec<usize> = (0..ROWS).filter(|&r| h[r] != f[r]).collect();
        assert_eq!(
            rows_differing,
            vec![ROWS - 1],
            "only the last row differs — every earlier row is the honest chain, so the refusal \
             below cannot be blamed on collateral damage"
        );
    }
}

/// ⚑ **AND THE FORGERY IS INSIDE THE LIMB WIDTH** — so a range lookup CANNOT be what refuses it.
///
/// This is the second wrong-reason failure this campaign hit: a falsifier refused by a range check
/// rather than by the gate under test passes while proving nothing about that gate. Every cell of
/// the forged trace is a genuine limb of a genuine field element.
#[test]
fn the_forgery_is_inside_the_limb_width() {
    for forged in [PALLAS_FORGED, VESTA_FORGED] {
        let f = cells(forged);
        for r in 0..ROWS {
            for c in 0..6 * SK {
                assert!(
                    f[r][c] < 256,
                    "row {r} input limb {c} = {} is outside the declared 8-bit width; a range \
                     lookup would refuse this trace and the thread gate would never be reached",
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
}

/// ⚑ **AND THE FORGED LAST ROW IS INTERNALLY HONEST.** Its accumulator input is a real projective
/// point (`G`), not a scribble — it is `rcbSoundRow` at `(G, G)`, so its own arithmetic holds. The
/// break is exactly and only at the seam.
#[test]
fn the_forged_last_row_breaks_only_the_seam() {
    for forged in [PALLAS_FORGED, VESTA_FORGED] {
        let f = cells(forged);
        let breaks: Vec<usize> = (0..ROWS - 1)
            .filter(|&r| {
                (0..SK).any(|i| {
                    f[r + 1][ACC_X + i] != f[r][OUT_X + i]
                        || f[r + 1][ACC_Y + i] != f[r][OUT_Y + i]
                        || f[r + 1][ACC_Z + i] != f[r][OUT_Z + i]
                })
            })
            .collect();
        assert_eq!(
            breaks,
            vec![ROWS - 2],
            "exactly one broken transition — the 6 -> 7 seam"
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// BOTH POLARITIES.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **POLARITY 1 — THE THREADED LADDER PROVES.** Eight chained rows of the sound RCB complete
/// addition, the accumulator carried across every seam by the emitted window gates, proved and
/// verified by the deployed `prove_vm_descriptor2` / `verify_vm_descriptor2`.
#[test]
fn the_threaded_ladder_proves_and_verifies() {
    for (json, text, who) in [
        (PALLAS_DESC_JSON, PALLAS_TRACE, "pallas"),
        (VESTA_DESC_JSON, VESTA_TRACE, "vesta"),
    ] {
        let d = descriptor(json);
        let t = trace(text);
        let proof = prove_vm_descriptor2(&d, &t, &[], &MemBoundaryWitness::default(), &[])
            .unwrap_or_else(|e| panic!("{who}: the honest threaded trace must prove: {e:?}"));
        verify_vm_descriptor2(&d, &proof, &[])
            .unwrap_or_else(|e| panic!("{who}: the honest threaded proof must verify: {e:?}"));
    }
}

/// ⚑ **POLARITY 2 — AND THE THREAD IS WHAT REFUSES THE UNCHAINED LADDER.**
///
/// The refusing gate, named: a `VmConstraint2::WindowGate { on_transition: true }` whose body is
/// `nxt(ACC_X + i) - loc(OUT_X + i)`, emitted by `PastaLadderThread.carryLeg`. Nothing else in the
/// descriptor can refuse this trace — every row's arithmetic holds
/// (`the_forged_last_row_breaks_only_the_seam`) and every cell is a legal limb
/// (`the_forgery_is_inside_the_limb_width`).
///
/// This is the whole distinction between a threaded fold and a re-pinned one, as a refusal.
#[test]
fn the_unchained_ladder_is_refused_by_the_thread() {
    for (json, text, who) in [
        (PALLAS_DESC_JSON, PALLAS_FORGED, "pallas"),
        (VESTA_DESC_JSON, VESTA_FORGED, "vesta"),
    ] {
        let d = descriptor(json);
        let t = trace(text);
        let r = prove_vm_descriptor2(&d, &t, &[], &MemBoundaryWitness::default(), &[]);
        assert!(
            r.is_err(),
            "{who}: eight independently honest rows whose accumulator does NOT chain must be \
             refused — and the only constraint that can refuse them is a transition window gate"
        );
    }
}

/// ⚑ **THE SAME TRACE WITHOUT THE THREAD WOULD BE ACCEPTED** — which is what makes the refusal
/// above a statement about the 96 window gates rather than about the fixture.
///
/// The standalone sound row (`dregg-pasta-pallas-complete-add-sound::v1`) is byte-for-byte this
/// descriptor minus the thread. Every row of the FORGED trace is an honest row of that descriptor,
/// so it proves there. The forgery is invisible to everything except the seam.
#[test]
fn without_the_thread_the_forged_trace_proves() {
    let unthreaded = descriptor(include_str!(
        "../descriptors/by-name/pasta-pallas-complete-add-sound.json"
    ));
    assert_eq!(unthreaded.trace_width, WIDTH);
    assert_eq!(
        unthreaded.constraints.len(),
        CONSTRAINTS - 96,
        "the standalone row IS the threaded one minus the 96 window gates"
    );
    let t = trace(PALLAS_FORGED);
    let proof = prove_vm_descriptor2(&unthreaded, &t, &[], &MemBoundaryWitness::default(), &[])
        .expect(
            "every row of the forged trace is an honest standalone row — so the UNTHREADED \
             descriptor accepts it, and the refusal in the test above is the thread's doing",
        );
    verify_vm_descriptor2(&unthreaded, &proof, &[]).expect("and the unthreaded proof verifies");
}
