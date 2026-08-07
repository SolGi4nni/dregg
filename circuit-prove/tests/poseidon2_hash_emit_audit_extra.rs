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
const GOLDEN_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/poseidon2-hash-arity2.json");

const IN0: usize = 0;
const IN1: usize = 1;
const DIGEST: usize = 2;
/// 3 after the E7 narrowing (the 7 exposed permutation-lane columns are gone).
const HASH_WIDTH: usize = 3;

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
