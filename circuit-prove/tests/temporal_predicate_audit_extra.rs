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

const GOLDEN_JSON: &str = r#"{"name":"dregg-temporal-predicate-gte::dsl-v1","ir":2,"trace_width":38,"public_input_count":4,"tables":[],"constraints":[{"t":"gate","body":{"t":"add","l":{"t":"var","v":2},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}},"r":{"t":"var","v":1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":3},"r":{"t":"add","l":{"t":"var","v":3},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"add","l":{"t":"var","v":4},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"add","l":{"t":"var","v":6},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"add","l":{"t":"var","v":7},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"var","v":8},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"add","l":{"t":"var","v":9},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"add","l":{"t":"var","v":10},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"var","v":11},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"var","v":12},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":13},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":14},"r":{"t":"add","l":{"t":"var","v":14},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"var","v":15},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":17},"r":{"t":"add","l":{"t":"var","v":17},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":18},"r":{"t":"add","l":{"t":"var","v":18},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":19},"r":{"t":"add","l":{"t":"var","v":19},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":20},"r":{"t":"add","l":{"t":"var","v":20},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":21},"r":{"t":"add","l":{"t":"var","v":21},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":22},"r":{"t":"add","l":{"t":"var","v":22},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":23},"r":{"t":"add","l":{"t":"var","v":23},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":24},"r":{"t":"add","l":{"t":"var","v":24},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":25},"r":{"t":"add","l":{"t":"var","v":25},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":26},"r":{"t":"add","l":{"t":"var","v":26},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":27},"r":{"t":"add","l":{"t":"var","v":27},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":28},"r":{"t":"add","l":{"t":"var","v":28},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":29},"r":{"t":"add","l":{"t":"var","v":29},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":30},"r":{"t":"add","l":{"t":"var","v":30},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":31},"r":{"t":"add","l":{"t":"var","v":31},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"add","l":{"t":"var","v":32},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":3}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2},"r":{"t":"var","v":4}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4},"r":{"t":"var","v":5}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8},"r":{"t":"var","v":6}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16},"r":{"t":"var","v":7}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32},"r":{"t":"var","v":8}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":64},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":128},"r":{"t":"var","v":10}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":256},"r":{"t":"var","v":11}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":512},"r":{"t":"var","v":12}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1024},"r":{"t":"var","v":13}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2048},"r":{"t":"var","v":14}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4096},"r":{"t":"var","v":15}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8192},"r":{"t":"var","v":16}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16384},"r":{"t":"var","v":17}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32768},"r":{"t":"var","v":18}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":19}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":131072},"r":{"t":"var","v":20}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":262144},"r":{"t":"var","v":21}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":524288},"r":{"t":"var","v":22}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1048576},"r":{"t":"var","v":23}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2097152},"r":{"t":"var","v":24}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4194304},"r":{"t":"var","v":25}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8388608},"r":{"t":"var","v":26}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16777216},"r":{"t":"var","v":27}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":33554432},"r":{"t":"var","v":28}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":67108864},"r":{"t":"var","v":29}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":134217728},"r":{"t":"var","v":30}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":268435456},"r":{"t":"var","v":31}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":536870912},"r":{"t":"var","v":32}},"r":{"t":"const","v":0}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":2}}}},{"t":"gate","body":{"t":"var","v":32}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":35},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":33}},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":36},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":34}},"r":{"t":"const","v":-1}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":33},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":35}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":34},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":36}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":1}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":33},"r":{"t":"const","v":-1}}},{"t":"boundary","row":"first","body":{"t":"var","v":34}},{"t":"pi_binding","row":"last","col":33,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":37,"pi_index":2},{"t":"pi_binding","row":"last","col":37,"pi_index":3}],"hash_sites":[],"ranges":[]}"#;

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
    let state_roots = [BabyBear::new(1000), BabyBear::new(1001), BabyBear::new(1002)];
    let num_steps = 3usize;
    let padded = 4usize;
    let final_root = state_roots[num_steps - 1];
    let mut trace = Vec::with_capacity(padded);
    for step in 0..padded {
        let value = if step < num_steps { values[step] } else { values[num_steps - 1] };
        let sr = if step < num_steps { state_roots[step] } else { final_root };
        trace.push(make_row(value, threshold, step, sr));
    }
    let pis = vec![BabyBear::new(padded as u32), BabyBear::new(threshold), state_roots[0], final_root];
    (trace, pis)
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    match r {
        Err(_) => true,
        Ok(Err(_)) => true,
        Ok(Ok(())) => false,
    }
}

/// AUDIT-A — pi[2] = initial_state_root forge. Isolates the row-0 STATE_ROOT PiBinding
/// (First, col37, pi2) — a distinct constraint NONE of the shipped 6 canaries exercise.
#[test]
fn audit_forged_initial_state_root_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, mut pis) = honest_trace();
    assert!(!rejects(&desc, &trace, &pis), "honest anchor must accept — else vacuous");
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
