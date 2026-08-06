//! ADVERSARIAL AUDIT — additional isolating tampers for the temporal-predicate emit gate.
//! Additive-only companion to `temporal_predicate_emit_gate.rs`. Re-uses the SAME byte-pinned
//! Lean-emitted golden JSON and drives the SAME real `prove_vm_descriptor2` / `verify_vm_descriptor2`.
//!
//! These target constraints the shipped 6 canaries did NOT isolate:
//!   * pi[2] = initial_state_root  → row-0 STATE_ROOT PiBinding (First,col37,pi2). The shipped
//!     canaries forge pi[0]/pi[1]/pi[3] but never pi[2].
//!   * the STEP_INDEX counter chain → C6 gate + T2 window gate.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::{Outcome, classify};

/// ⚑ **THE EMITTED ARTIFACT ITSELF, NOT A COPY OF IT (2026-08-06).** This was an inline
/// `r#"…"#` transcription of the Lean `#guard` bytes, and the `challenges` flag day
/// (2026-08-05) broke it along with 27 siblings: the artifact under
/// `circuit/descriptors/` was re-emitted, the literal was not, and
/// `parse_vm_descriptor2` refused it with `ir:2 descriptor missing "challenges"`. An
/// inline golden is a copy that no re-emit reaches, so every flag day breaks exactly
/// that set again — the fix is to have no copy. `check-emit-gate-weld.py` still gates
/// the literals that remain (the descriptors with no checked-in artifact to name), and
/// `check-descriptor-drift.sh` gates this file against its Lean author.
const GOLDEN_JSON: &str = include_str!("../../circuit/descriptors/by-name/temporal-predicate.json");

const VALUE: usize = 0;
const THRESHOLD: usize = 1;
const DIFF: usize = 2;
const DIFF_BITS_START: usize = 3;
const NUM_DIFF_BITS: usize = 30;
const ACCUMULATOR: usize = 33;
const STEP_INDEX: usize = 34;
const ACC_PLUS_ONE: usize = 35;
const STEP_PLUS_ONE: usize = 36;
const STATE_ROOT: usize = 37;
const TRACE_WIDTH: usize = 38;

const PI_INITIAL_STATE_ROOT: usize = 2;

fn make_row(value: u32, threshold: u32, step: usize, state_root: BabyBear) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
    row[VALUE] = BabyBear::new(value);
    row[THRESHOLD] = BabyBear::new(threshold);
    let diff = BabyBear::new(value) - BabyBear::new(threshold);
    row[DIFF] = diff;
    let diff_u = diff.as_u32();
    for i in 0..NUM_DIFF_BITS {
        row[DIFF_BITS_START + i] = BabyBear::new((diff_u >> i) & 1);
    }
    let acc = (step + 1) as u32;
    row[ACCUMULATOR] = BabyBear::new(acc);
    row[STEP_INDEX] = BabyBear::new(step as u32);
    row[ACC_PLUS_ONE] = BabyBear::new(acc + 1);
    row[STEP_PLUS_ONE] = BabyBear::new(step as u32 + 1);
    row[STATE_ROOT] = state_root;
    row
}

fn honest_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let threshold = 50u32;
    let values = [100u32, 100, 100];
    let state_roots = [
        BabyBear::new(1000),
        BabyBear::new(1001),
        BabyBear::new(1002),
    ];
    let num_steps = 3usize;
    let padded = 4usize;
    let final_root = state_roots[num_steps - 1];
    let mut trace = Vec::with_capacity(padded);
    for step in 0..padded {
        let value = if step < num_steps {
            values[step]
        } else {
            values[num_steps - 1]
        };
        let sr = if step < num_steps {
            state_roots[step]
        } else {
            final_root
        };
        trace.push(make_row(value, threshold, step, sr));
    }
    let pis = vec![
        BabyBear::new(padded as u32),
        BabyBear::new(threshold),
        state_roots[0],
        final_root,
    ];
    (trace, pis)
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("rejects", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// AUDIT-A — pi[2] = initial_state_root forge. Isolates the row-0 STATE_ROOT PiBinding
/// (First, col37, pi2) — a distinct constraint NONE of the shipped 6 canaries exercise.
#[test]
fn audit_forged_initial_state_root_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, mut pis) = honest_trace();
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest anchor must accept — else vacuous"
    );
    pis[PI_INITIAL_STATE_ROOT] = BabyBear::new(88888); // real row-0 STATE_ROOT is 1000
    assert!(
        rejects(&desc, &trace, &pis),
        "a forged initial_state_root PI must be REJECTED by the row-0 STATE_ROOT PiBinding (pi2)"
    );
}

/// AUDIT-B — the STEP_INDEX counter chain. Gap the step_index at a middle (transition) row.
/// The C6 gate (step_plus_one - step_index - 1) AND the T2 window gate
/// (next.step_index - local.step_plus_one) are UNSAT. Distinct from the shipped ACCUMULATOR
/// canary (which hits C5/T1).
#[test]
fn audit_broken_step_index_counter_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    assert!(!rejects(&desc, &trace, &pis), "honest anchor");
    let mut bad = trace.clone();
    bad[1][STEP_INDEX] = BabyBear::new(7); // break the step chain at row 1 (a transition row)
    assert!(
        rejects(&desc, &bad, &pis),
        "a gapped step_index must be REJECTED by the C6 gate + T2 window gate"
    );
}
