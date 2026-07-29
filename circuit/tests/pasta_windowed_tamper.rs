//! # The windowed Pallas RCB AIR must go RED. Green on an honest witness proves nothing alone.
//!
//! `pasta_windowed_prove.rs` shows the deployed prover ACCEPTS Lean-generated honest witnesses of
//! `dregg-pasta-rcb-windowed::v1`. On its own that is compatible with the AIR being vacuous on
//! this trace shape — an AIR that constrains nothing accepts every witness, and would have
//! produced exactly the same seven green tests.
//!
//! So this file is the other half: single-cell tampers of the SAME honest 64-row fixture, each of
//! which the deployed prover must REFUSE. Every tamper targets a cell some emitted Lean constraint
//! reads, and names which one.
//!
//! ⚠ The tampered row is row 1 — never row 0 (whose accumulator is a free input) and never the
//! LAST row, whose gates `builder.when_transition()` does not reach. A tamper on the last row is
//! EXPECTED to pass and is asserted to, below, because that exemption is a real property of the
//! deployed evaluator and a reader should see it stated rather than discover it.
//!
//! Substrate: the AIR is Lean-authored (`Dregg2.Circuit.Emit.PastaMsmWindowed`). Nothing here
//! authors a constraint; these tests move trace CELLS and ask the deployed prover.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
};

const DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-rcb-windowed.json");
const TRACE_64: &str = include_str!("../descriptors/by-name/pasta-rcb-windowed-trace-64.txt");

/// Column bases, mirroring `PastaMsmWindowed` §1.
const COL_OUTX: usize = 234;
const COL_ACCX: usize = 442;
const COL_OPX: usize = 469;
const COL_SRCX: usize = 496;
const COL_BIT: usize = 523;
const COL_DBL: usize = 524;
const WIDTH: usize = 525;

fn descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(DESC_JSON).expect("the deployed checker must parse the Lean descriptor")
}

fn fixture() -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = TRACE_64
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(rows.len(), 64);
    assert!(rows.iter().all(|r| r.len() == WIDTH));
    rows
}

fn proves(trace: &[Vec<BabyBear>]) -> Result<(), String> {
    prove_vm_descriptor2(
        &descriptor(),
        trace,
        &[],
        &MemBoundaryWitness::default(),
        &[],
    )
    .map(|_| ())
}

/// Bump one cell by one and ask the deployed prover.
fn bump_at(row: usize, col: usize) -> Result<(), String> {
    let mut t = fixture();
    let cur = t[row][col].as_u32();
    t[row][col] = BabyBear::new(cur + 1);
    proves(&t)
}

/// ⚑⚑ THE VACUITY PROBE, and the reason every other test in this file is currently RED.
///
/// An all-zeros trace is not a witness of anything: constraint #30 (a `pallasCompleteAdd` gate)
/// and #42 (a `threadGates` window gate) do not vanish on it. Evaluating the emitted descriptor
/// directly, mod BabyBear, confirms that — 0 of 45 constraints are violated by the honest Lean
/// witness, 2 of 45 by a single-cell tamper of it.
///
/// The deployed prover PROVES the all-zeros trace anyway, in ~0.1 s.
///
/// So `pasta_windowed_prove.rs`'s greens do NOT say the prover checked the Lean AIR. They say a
/// FRI proof over the trace commitment was produced. The constraint system is not binding on the
/// IR-v2 path, and this is NOT specific to this descriptor: 17 of the 68
/// `descriptor_ir2::tests::*` unit tests are red, every one of them a `*_refuses` / `*_rejects`
/// test, and those build their descriptors in Rust without touching the JSON parser.
#[test]
fn all_zeros_trace_must_not_prove() {
    let zeros = vec![vec![BabyBear::new(0); WIDTH]; 64];
    assert!(
        proves(&zeros).is_err(),
        "AN ALL-ZEROS TRACE PROVED against a 45-constraint descriptor. The IR-v2 prover is \
         fail-open: it is not enforcing the AIR at all. Every `prove_vm_descriptor2` green in \
         this repo is, until this is fixed, a statement about a FRI commitment and not about \
         the constraint system."
    );
}

/// The CONTROL. Without this, a tamper test that goes red proves only that something is broken.
#[test]
fn honest_fixture_still_proves() {
    proves(&fixture()).expect("the honest Lean witness must prove");
}

/// ⚑ Every single-cell tamper on a CONSTRAINED row must be refused, and each names the emitted
/// Lean constraint family that catches it.
#[test]
fn single_cell_tampers_are_all_refused() {
    let cases: [(usize, usize, &str); 7] = [
        // `pallasCompleteAdd`'s 33 gates: the row's output no longer is the complete add of its
        // inputs. Also breaks the 3 `threadGates`, which read exactly these columns.
        (
            1,
            COL_OUTX,
            "X3 output limb — pallasCompleteAdd + threadGates",
        ),
        (1, COL_OUTX + 27, "Y3 output limb — pallasCompleteAdd"),
        // The add's first operand.
        (
            1,
            COL_ACCX,
            "accumulator limb — pallasCompleteAdd + threadGates",
        ),
        // The add's second operand, which the selector pins.
        (
            1,
            COL_OPX,
            "addend limb — condPointGates + pallasCompleteAdd",
        ),
        // `binGate BIT` — 2 is not a bit.
        (1, COL_BIT, "conditional bit — binGate BIT"),
        // `binGate DBL` — likewise.
        (1, COL_DBL, "doubling selector — binGate DBL"),
        // The source point on a row whose bit is set: `condPointGates` forces OP = SRC, so moving
        // SRC alone breaks the selector.
        (1, COL_SRCX, "source limb — condPointGates"),
    ];
    for (row, col, why) in cases {
        assert!(
            bump_at(row, col).is_err(),
            "TAMPER ACCEPTED at row {row} col {col} ({why}) — the AIR does not constrain this cell"
        );
    }
}

/// ⚑ The DOUBLING PIN bites on a real trace, not only in the Lean `#guard`s: asserting `DBL = 1`
/// on a conditional-add row whose source is NOT the accumulator is refused by `dblPinHead`.
#[test]
fn forged_doubling_row_is_refused() {
    let mut t = fixture();
    // Row 1 is a conditional-add row (row 0 is the plane's doubling row).
    assert_eq!(t[1][COL_DBL].as_u32(), 0, "row 1 must be a cond-add row");
    t[1][COL_DBL] = BabyBear::new(1);
    assert!(
        proves(&t).is_err(),
        "a forged doubling row was ACCEPTED — dblPinHead does not bite"
    );
}

/// ⚑ The FREE-TERM FORGERY on a real trace: a prover that clears the bit but leaves the addend in
/// place would add a term it did not pay for. `condPointGates` forces the addend to `O` when the
/// bit is off, so this is refused.
#[test]
fn free_term_forgery_is_refused() {
    let mut t = fixture();
    let bit_row = (0..63)
        .find(|&i| t[i][COL_BIT].as_u32() == 1 && t[i][COL_DBL].as_u32() == 0)
        .expect("some conditional-add row has its bit set");
    t[bit_row][COL_BIT] = BabyBear::new(0);
    assert!(
        proves(&t).is_err(),
        "the free-term forgery was ACCEPTED at row {bit_row} — condPointGates does not bite"
    );
}

/// ⚑ The THREAD bites: re-pointing the next row's accumulator away from this row's output breaks
/// the 3 emitted `windowGate`s even though every row-local gate of that row still holds.
///
/// The tamper rewrites row 2's accumulator group to row 0's, which is a perfectly well-formed
/// point — so this is not caught by any row-local check, only by the cross-row window.
#[test]
fn broken_thread_is_refused() {
    let mut t = fixture();
    for j in 0..27 {
        let borrowed = t[0][COL_ACCX + j];
        t[2][COL_ACCX + j] = borrowed;
    }
    assert!(
        proves(&t).is_err(),
        "a broken accumulator thread was ACCEPTED — the windowGates do not bite"
    );
}

/// The LAST row's gates are outside `when_transition`, so a tamper there is EXPECTED to prove.
/// Asserted rather than left implicit: it is the reason the witness generator must emit `H-1`
/// honest rows and why a pad row is a real RCB add rather than a zero-fill.
#[test]
fn last_row_is_exempt_by_construction() {
    let mut t = fixture();
    let last = t.len() - 1;
    let cur = t[last][COL_OUTX].as_u32();
    t[last][COL_OUTX] = BabyBear::new(cur + 1);
    assert!(
        proves(&t).is_ok(),
        "the last row turned out to be constrained — then the pad discipline in \
         EmitPastaWindowedTrace.lean is stricter than it needs to be, which is safe but the \
         comment explaining it is wrong"
    );
}
