//! ADDITIVE adversarial audit tamper for `poseidon2HashDesc` — the IN1 boundary pin (PI[1]).
//! The shipped gate (`poseidon2_hash_emit_gate.rs`) exercises the IN0 pin (4d, PI[0]) but NEVER the
//! IN1 pin. This isolates `in1Pin` (col 1 -> pi_index 1): honest trace, forged PI[1] -> UNSAT.
//! Plus a positive re-check that the honest witness accepts (non-vacuity guard).

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_2_to_1;

const GOLDEN_JSON: &str = r#"{"name":"poseidon2-hash-arity2::poseidon2-v1","ir":2,"trace_width":10,"public_input_count":3,"tables":[],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":0},{"t":"var","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":2},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":8},{"t":"var","v":9}]},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":2,"pi_index":2}],"hash_sites":[],"ranges":[]}"#;

const IN0: usize = 0;
const IN1: usize = 1;
const DIGEST: usize = 2;
const HASH_WIDTH: usize = 10;

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

fn honest_trace(a: BabyBear, b: BabyBear) -> (Vec<Vec<BabyBear>>, BabyBear) {
    let digest = hash_2_to_1(a, b);
    let mut row = vec![BabyBear::ZERO; HASH_WIDTH];
    row[IN0] = a;
    row[IN1] = b;
    row[DIGEST] = digest;
    (vec![row.clone(), row.clone(), row.clone(), row], digest)
}

/// NEW ISOLATING TAMPER: forge PI[1] (the IN1 boundary pin) on an otherwise honest trace.
/// The pin `IN1 == PI[1]` (col 1 -> pi_index 1) is violated -> UNSAT. Untested by the shipped gate.
#[test]
fn forged_in1_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let a = BabyBear::new(1001);
    let b = BabyBear::new(2002);
    let (trace, digest) = honest_trace(a, b);
    // non-vacuity: honest witness accepts.
    assert!(
        !rejects(&desc, &trace, &[a, b, digest]),
        "honest witness must accept — else vacuous"
    );
    // forge only PI[1]; trace IN1 still = b, so the pin col1==PI[1] must fail.
    assert!(
        rejects(&desc, &trace, &[a, b + BabyBear::ONE, digest]),
        "a forged IN1 PI must be REJECTED by the in1Pin boundary constraint"
    );
}
