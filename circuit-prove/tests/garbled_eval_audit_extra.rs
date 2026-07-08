//! ADVERSARIAL AUDIT — extra isolating tampers the implementer did not write.
//! Additive-only; reuses the exact GOLDEN_JSON from garbled_eval_emit_gate.rs.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, WindowExpr, WindowGateSpec,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

const GOLDEN_JSON: &str = r#"{"name":"dregg-garbled-evaluation-extended-dsl-v1","ir":2,"trace_width":56,"public_input_count":8,"tables":[],"constraints":[{"t":"pi_binding","row":"first","col":41,"pi_index":0},{"t":"pi_binding","row":"first","col":42,"pi_index":1},{"t":"pi_binding","row":"first","col":43,"pi_index":2},{"t":"pi_binding","row":"first","col":44,"pi_index":3},{"t":"pi_binding","row":"first","col":45,"pi_index":4},{"t":"pi_binding","row":"first","col":46,"pi_index":5},{"t":"pi_binding","row":"first","col":47,"pi_index":6},{"t":"pi_binding","row":"first","col":48,"pi_index":7},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":33},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":25}},"r":{"t":"var","v":17}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":34},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":26}},"r":{"t":"var","v":18}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":35},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":27}},"r":{"t":"var","v":19}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":36},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":28}},"r":{"t":"var","v":20}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":29}},"r":{"t":"var","v":21}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":38},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":30}},"r":{"t":"var","v":22}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":39},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":31}},"r":{"t":"var","v":23}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":40},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":32}},"r":{"t":"var","v":24}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":49},"r":{"t":"add","l":{"t":"var","v":49},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":50},"r":{"t":"add","l":{"t":"var","v":50},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":51},"r":{"t":"add","l":{"t":"var","v":51},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":52},"r":{"t":"add","l":{"t":"var","v":52},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":53},"r":{"t":"add","l":{"t":"var","v":53},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":55},"r":{"t":"add","l":{"t":"var","v":55},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":49},"r":{"t":"add","l":{"t":"var","v":50},"r":{"t":"add","l":{"t":"var","v":51},"r":{"t":"add","l":{"t":"var","v":52},"r":{"t":"const","v":-1}}}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":33}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":34}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":35}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":36}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":37}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":38}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":39}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":40}}}}},{"t":"boundary","row":"first","body":{"t":"var","v":54}}],"hash_sites":[],"ranges":[]}"#;

fn left(i: usize) -> usize { i }
fn right(i: usize) -> usize { 8 + i }
fn hash_out(i: usize) -> usize { 17 + i }
fn table_entry(i: usize) -> usize { 25 + i }
fn output(i: usize) -> usize { 33 + i }
const CIRCUIT_COMMITMENT: usize = 41;
const OUTPUT_LABEL_HASH: usize = 45;
const IS_AND: usize = 49;
const CHAIN_FLAG: usize = 53;
const GATE_INDEX_DELTA: usize = 54;
const IS_PADDING: usize = 55;
const GARBLED_WIDTH: usize = 56;
const PI_COUNT: usize = 8;

fn pis() -> Vec<BabyBear> {
    (0..PI_COUNT).map(|j| BabyBear::new(10 + j as u32)).collect()
}

fn real_row(left_seed: &[u32; 8], right_base: u32, hash_base: u32, output_base: u32, is_and: u32, chain: u32, delta: u32) -> Vec<BabyBear> {
    let pi = pis();
    let mut r = vec![BabyBear::ZERO; GARBLED_WIDTH];
    for i in 0..8 {
        r[left(i)] = BabyBear::new(left_seed[i]);
        r[right(i)] = BabyBear::new(right_base + i as u32);
        let h = hash_base + i as u32;
        let o = output_base + i as u32;
        r[hash_out(i)] = BabyBear::new(h);
        r[output(i)] = BabyBear::new(o);
        r[table_entry(i)] = BabyBear::new(o + h);
    }
    for j in 0..4 {
        r[CIRCUIT_COMMITMENT + j] = pi[j];
        r[OUTPUT_LABEL_HASH + j] = pi[4 + j];
    }
    r[IS_AND] = BabyBear::new(is_and);
    r[CHAIN_FLAG] = BabyBear::new(chain);
    r[GATE_INDEX_DELTA] = BabyBear::new(delta);
    r[IS_PADDING] = BabyBear::ZERO;
    r
}

fn padding_row() -> Vec<BabyBear> {
    let pi = pis();
    let mut r = vec![BabyBear::ZERO; GARBLED_WIDTH];
    for j in 0..4 {
        r[CIRCUIT_COMMITMENT + j] = pi[j];
        r[OUTPUT_LABEL_HASH + j] = pi[4 + j];
    }
    r[IS_PADDING] = BabyBear::ONE;
    r
}

fn honest_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let row0 = real_row(&[100, 101, 102, 103, 104, 105, 106, 107], 200, 300, 400, 1, 1, 0);
    let row0_out: [u32; 8] = std::array::from_fn(|i| 400 + i as u32);
    let row1 = real_row(&row0_out, 250, 350, 500, 1, 0, 1);
    let trace = vec![row0, row1, padding_row(), padding_row()];
    (trace, pis())
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], p: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, p, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, p)
    }));
    match r {
        Err(_) => true,
        Ok(Err(_)) => true,
        Ok(Ok(())) => false,
    }
}

/// EXTRA CANARY 1 (isolates the OUTPUT_LABEL_HASH pin, col 45 / pi_index 4 — the
/// implementer only tampered pi[0]/col41). Forging pi[4] must be caught by the
/// second PI block's first-row pi_binding.
#[test]
fn forged_output_label_hash_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, p) = honest_trace();
    assert!(!rejects(&desc, &trace, &p), "honest witness must be accepted (non-vacuity)");
    let mut forged = p.clone();
    forged[4] = forged[4] + BabyBear::ONE;
    assert!(rejects(&desc, &trace, &forged), "a forged output_label_hash PI must be REJECTED (col 45 pi_binding)");
}

/// EXTRA CANARY 2 (isolates the hash_out free-witness column via the decryption gate).
/// hash_out appears ONLY in the decryption gate; bumping it off `output = table - hash`
/// must fire the C9 decryption gate. (The implementer bumped table_entry; this bumps the
/// other decryption operand to confirm the gate constrains hash_out too.)
#[test]
fn forged_hash_out_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, p) = honest_trace();
    assert!(!rejects(&desc, &trace, &p), "honest witness must be accepted (non-vacuity)");
    let mut bad = trace.clone();
    bad[0][hash_out(0)] = bad[0][hash_out(0)] + BabyBear::ONE;
    assert!(rejects(&desc, &bad, &p), "a forged hash_out must be REJECTED (decryption gate)");
}

/// PROBE of the documented every-row -> first-row residual. The DSL pins the
/// commitment PI on EVERY row (ConstraintExpr::PiBinding is per-row); this emit pins
/// only the FIRST row. Tampering a NON-first row's commitment column should therefore
/// be ACCEPTED by the emit (whereas the DSL would reject). This documents that the
/// residual is a genuine faithfulness weakening — but it does NOT let a wrong PUBLIC
/// claim through: the first row still binds the commitment to the public input.
#[test]
fn nonfirst_row_commitment_drift_is_accepted_documenting_residual() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, p) = honest_trace();
    assert!(!rejects(&desc, &trace, &p), "honest witness must be accepted");
    let mut drift = trace.clone();
    // row 1 (non-first) commitment column diverges from the PI.
    drift[1][CIRCUIT_COMMITMENT] = drift[1][CIRCUIT_COMMITMENT] + BabyBear::ONE;
    let accepted = !rejects(&desc, &drift, &p);
    // We assert the observed behavior to make the residual explicit in the test record.
    assert!(accepted, "emit pins commitment PI on FIRST row only (documented residual): non-first-row drift is not caught");
}
