//! # `prove_vm_descriptor2` is FAIL-CLOSED, in every build profile.
//!
//! ## The property
//!
//! **`prove_vm_descriptor2(desc, trace, ..)` returns `Ok` ⟹ the returned proof VERIFIES.**
//!
//! Equivalently: a producer whose witness does not satisfy the AIR learns so from the `Result`,
//! rather than shipping a proof that its consumer will reject.
//!
//! ## Why this file exists
//!
//! It did not hold, from `934258ea0` (2026-06-24) to 2026-07-29 — 35 days — under `--release`
//! only. That commit was a perf sweep, self-described as "result-identical", and it moved the
//! producer-side self-verify behind `cfg!(debug_assertions)`. Its justification was that "the
//! in-trace replay above, also gated by `check`, already eagerly refuses a bad witness
//! fail-closed". The replay does no such thing: it covers the exact-public manifests, the submask
//! bit blocks, and the mem / umem / map-op witnesses, and it never evaluates one algebraic
//! constraint — no `Gate`, `Boundary`, `PiBinding`, `Transition` or `WindowGate`.
//!
//! p3's own checks do not cover the gap either. `prove_batch`'s row-by-row `check_constraints` and
//! its LogUp balance check are both `#[cfg(debug_assertions)]`, and the balance check additionally
//! runs only for instances that declare lookups (`batch-stark/src/prover.rs`).
//!
//! So for a descriptor made only of algebraic gates, a release build had NOTHING checking the
//! witness. `dregg-pasta-rcb-windowed::v1` is exactly that shape — 45 constraints, zero lookups —
//! and `prove_vm_descriptor2` returned `Ok` for an ALL-ZEROS trace.
//!
//! ## What was NOT wrong
//!
//! The constraint system. Every one of those proofs was refused by `verify_vm_descriptor2` with
//! `OodEvaluationMismatch { index: Some(0) }` — the Main AIR. The AIR bound its constraints the
//! whole time; a green `prove` simply stopped being evidence of it. `verify_refuses_*` below pins
//! that half so a future reader does not have to re-derive it.
//!
//! Substrate: nothing here authors a constraint. The pasta AIR is Lean-authored
//! (`Dregg2.Circuit.Emit.PastaMsmWindowed`); these tests move trace CELLS and ask the deployed
//! prover and the deployed verifier.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};

/// The algebraic-only descriptor: 45 constraints, ZERO lookups. This is the shape p3's debug
/// lookup check cannot see even in a debug build, so it is the strictest witness of the property.
const DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-rcb-windowed.json");
const TRACE_64: &str = include_str!("../descriptors/by-name/pasta-rcb-windowed-trace-64.txt");

const WIDTH: usize = 525;
/// The X3 output limb of `pallasCompleteAdd`; row 1 is constrained (row 0's accumulator is a free
/// input and the LAST row is exempted by `when_transition`).
const COL_OUTX: usize = 234;

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

fn prove(trace: &[Vec<BabyBear>]) -> Result<(), String> {
    let desc = descriptor();
    prove_vm_descriptor2(&desc, trace, &[], &MemBoundaryWitness::default(), &[]).map(|_| ())
}

/// Prove, and if a proof came back, ALSO verify it. The point of the pair is the implication:
/// `Ok(prove)` must never be followed by `Err(verify)`.
fn prove_then_verify(trace: &[Vec<BabyBear>]) -> Result<(), String> {
    let desc = descriptor();
    let proof = prove_vm_descriptor2(&desc, trace, &[], &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(&desc, &proof, &[])
}

fn tampered() -> Vec<Vec<BabyBear>> {
    let mut t = fixture();
    t[1][COL_OUTX] = BabyBear::new(t[1][COL_OUTX].as_u32() + 1);
    t
}

fn all_zeros() -> Vec<Vec<BabyBear>> {
    vec![vec![BabyBear::new(0); WIDTH]; 64]
}

/// The CONTROL. Without it every assertion below is satisfiable by a path that refuses everything.
#[test]
fn honest_witness_proves_and_verifies() {
    prove_then_verify(&fixture()).expect("the honest Lean witness must prove AND verify");
}

/// ⚑⚑ **THE FALSIFIER.** An all-zeros trace is not a witness of anything — evaluating the emitted
/// descriptor directly mod BabyBear, 2 of its 45 constraints are violated by it. `prove` must say
/// so.
#[test]
fn prove_refuses_an_all_zeros_trace() {
    let e = prove(&all_zeros()).expect_err(
        "AN ALL-ZEROS TRACE PROVED against a 45-constraint descriptor. `prove_vm_descriptor2` is \
         fail-OPEN again: it minted a proof for a witness that does not satisfy the AIR, and a \
         producer cannot tell. Check for `cfg!(debug_assertions)` having crept back onto the \
         self-verify in `descriptor_ir2::prove_vm_descriptor2_inner`.",
    );
    assert!(
        e.contains("self-verify failed"),
        "the all-zeros trace was refused for the WRONG reason (a shape fault, not a constraint \
         verdict): {e}"
    );
}

/// ⚑⚑ **THE FALSIFIER, single-cell form.** One cell of the honest witness, bumped by one, on a
/// row `when_transition` reaches. Two emitted Lean constraints read it.
#[test]
fn prove_refuses_a_single_cell_tamper() {
    let e = prove(&tampered()).expect_err(
        "A SINGLE-CELL TAMPER PROVED. `prove_vm_descriptor2` is fail-OPEN: it minted a proof for \
         a witness that does not satisfy the AIR. See the module header.",
    );
    assert!(
        e.contains("self-verify failed"),
        "the tamper was refused for the WRONG reason (a shape fault, not a constraint verdict): {e}"
    );
}

/// The implication stated directly: on every input this file knows about, `prove` returning `Ok`
/// is followed by `verify` returning `Ok`. A fail-open `prove` breaks this even when the two
/// tests above are read as merely "some error came back".
#[test]
fn a_proof_that_was_minted_always_verifies() {
    for (name, trace) in [
        ("honest", fixture()),
        ("all-zeros", all_zeros()),
        ("single-cell tamper", tampered()),
    ] {
        if prove(&trace).is_ok() {
            prove_then_verify(&trace).unwrap_or_else(|e| {
                panic!(
                    "{name}: `prove_vm_descriptor2` returned Ok and the proof it returned DOES \
                     NOT VERIFY ({e}). A producer that cannot distinguish a good witness from a \
                     bad one ships proofs its consumers reject."
                )
            });
        }
    }
}

/// The other half, pinned so it is not re-derived: the CONSTRAINT SYSTEM was never the problem.
/// Even while `prove` was fail-open, the deployed verifier refused these proofs — and the refusal
/// lands on instance 0, the Main AIR carrying the Lean-emitted gates. The producer surfaces that
/// verdict verbatim, so the wording is checkable from the public entry alone.
#[test]
fn the_refusal_is_the_main_airs_own_verdict() {
    for (name, trace) in [("all-zeros", all_zeros()), ("tamper", tampered())] {
        let e = prove(&trace).expect_err("must be refused");
        assert!(
            e.contains("OodEvaluationMismatch"),
            "{name}: refused, but not on constraint grounds: {e}"
        );
        assert!(
            e.contains("index: Some(0)"),
            "{name}: the refusal must land on instance 0 — the Main AIR that carries the \
             Lean-emitted constraints — not on a side table: {e}"
        );
    }
}
