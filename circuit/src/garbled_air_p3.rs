//! POC: `GarbledEvaluationAir` ported from the hand-rolled `crate::stark::StarkAir`
//! trait to a real Plonky3 `p3-air::Air<AB>` proven through the audited
//! `p3-uni-stark` + `p3-fri` backend (`crate::plonky3_prover::create_config`).
//!
//! This is the de-risking proof-of-concept for the stark.rs -> plonky3 migration.
//! It demonstrates the full porting recipe on the simplest pure-arithmetic AIR:
//!
//!   * `StarkAir::width`            -> `BaseAir::width`
//!   * `StarkAir::eval_constraints` -> `Air::eval` (symbolic, per-constraint
//!                                     `builder.assert_zero`; alpha folding is the
//!                                     verifier's job, dropped here)
//!   * `StarkAir::boundary_constraints` -> `builder.when_first_row()/when_last_row()`
//!   * trace generation             -> a `RowMajorMatrix<P3BabyBear>` builder,
//!                                     padded to a power of two.
//!
//! The original `GarbledEvaluationAir` (degree 2, `has_chain_continuity()=false`,
//! no native hashing inside its constraints) maps mechanically: every constraint
//! is a linear/quadratic combination of trace cells and public values.
//!
//! Soundness is checked by the `*_rejected` tests: a tampered trace (forged
//! output label, or a public-input claim that does not match the bound trace
//! cell) must fail `verify`.

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::{prove, verify};

use crate::field::BabyBear;
use crate::garbled_air::{GARBLED_EVAL_AIR_WIDTH, col};
use crate::plonky3_prover::{DreggProof, create_config, to_p3};

/// Plonky3-native garbled-evaluation AIR. Same column layout as
/// `crate::garbled_air::GarbledEvaluationAir`, but emits symbolic constraints.
///
/// Public inputs: `[circuit_commitment[0..4], output_label_hash[0..4]]` (8 felts).
pub struct P3GarbledEvaluationAir;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for P3GarbledEvaluationAir {
    fn width(&self) -> usize {
        GARBLED_EVAL_AIR_WIDTH // 49
    }

    fn num_public_values(&self) -> usize {
        8 // [circuit_commitment[0..4], output_label_hash[0..4]]
    }
}

impl<AB: AirBuilder> Air<AB> for P3GarbledEvaluationAir {
    fn eval(&self, builder: &mut AB) {
        // Materialize all needed cells/public values into owned `AB::Expr`
        // first, so the immutable borrows of `builder.main()` /
        // `builder.public_values()` are dropped before the mutable
        // `builder.assert_eq` calls.
        let (cc, olh, dec): (
            [AB::Expr; 4],
            [AB::Expr; 4],
            [(AB::Expr, AB::Expr, AB::Expr); 8],
        ) = {
            let main = builder.main();
            let local = main.current_slice();
            let cc = core::array::from_fn(|i| local[col::CIRCUIT_COMMITMENT + i].into());
            let olh = core::array::from_fn(|i| local[col::OUTPUT_LABEL_HASH + i].into());
            let dec = core::array::from_fn(|i| {
                (
                    local[col::output(i)].into(),
                    local[col::table_entry(i)].into(),
                    local[col::hash_out(i)].into(),
                )
            });
            (cc, olh, dec)
        };
        let pv: [AB::Expr; 8] = {
            let public_values = builder.public_values();
            core::array::from_fn(|i| public_values[i].into())
        };

        // --- C1-C4: circuit_commitment[0..4] matches public_inputs[0..4] ---
        // --- C5-C8: output_label_hash[0..4] matches public_inputs[4..8] ---
        // Mirrors StarkAir::eval_constraints C1-C8 AND the boundary constraints
        // (the original binds these on row 0; since they are constant across all
        // rows in the trace generator, asserting them on every row is equivalent
        // and strictly stronger). We additionally pin them to the public values.
        for (i, c) in cc.into_iter().enumerate() {
            builder.assert_eq(c, pv[i].clone());
        }
        for (i, o) in olh.into_iter().enumerate() {
            builder.assert_eq(o, pv[4 + i].clone());
        }

        // --- C9-C16: Decryption correctness ---
        // output_label[i] == table_entry[i] - hash_out[i]   for i in 0..8
        for (out, entry, hout) in dec.into_iter() {
            builder.assert_eq(out, entry - hout);
        }
    }
}

/// Convert a `Vec<Vec<BabyBear>>` trace (the StarkAir-era layout) into a padded
/// `RowMajorMatrix<P3BabyBear>` (power-of-two height, min 2 rows).
pub fn trace_to_p3_matrix(trace: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
    assert!(!trace.is_empty());
    let width = trace[0].len();
    let target = trace.len().next_power_of_two().max(2);
    let mut values: Vec<P3BabyBear> = Vec::with_capacity(target * width);
    for row in trace {
        debug_assert_eq!(row.len(), width);
        values.extend(row.iter().map(|&v| to_p3(v)));
    }
    // Pad by repeating the last row (a NoOp-equivalent: the decryption identity
    // and the constant PI-binding columns still hold on a duplicated row).
    let last = trace.last().unwrap();
    for _ in trace.len()..target {
        values.extend(last.iter().map(|&v| to_p3(v)));
    }
    RowMajorMatrix::new(values, width)
}

/// Prove a garbled-evaluation trace through the real p3-fri backend.
pub fn prove_garbled_p3(trace: &[Vec<BabyBear>], public_inputs: &[BabyBear]) -> DreggProof {
    let config = create_config();
    let air = P3GarbledEvaluationAir;
    let matrix = trace_to_p3_matrix(trace);
    let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    prove(&config, &air, matrix, &p3_public)
}

/// Verify a garbled-evaluation proof through the real p3-fri backend.
pub fn verify_garbled_p3(proof: &DreggProof, public_inputs: &[BabyBear]) -> Result<(), String> {
    let config = create_config();
    let air = P3GarbledEvaluationAir;
    let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
    verify(&config, &air, proof, &p3_public).map_err(|e| format!("p3 verify failed: {:?}", e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint_prover::Air as ConstraintAir;
    use crate::field::BabyBear;
    use crate::garbled::{COMPARISON_BITS, evaluate_garbled_circuit, garble_comparison_circuit};
    use crate::garbled_air::GarbledEvaluationAir;

    /// Build a real garbled-evaluation trace via the existing StarkAir generator,
    /// so the POC proves the *same statement* the legacy AIR proved.
    fn real_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let threshold = 100u32;
        let prover_value = 150u32;
        let (circuit, secrets) = garble_comparison_circuit(threshold, COMPARISON_BITS);
        let prover_labels: Vec<[BabyBear; 8]> = (0..COMPARISON_BITS)
            .map(|bit_idx| {
                let bit = (prover_value >> bit_idx) & 1;
                if bit == 0 {
                    secrets.prover_label_pairs[bit_idx].0
                } else {
                    secrets.prover_label_pairs[bit_idx].1
                }
            })
            .collect();
        let eval = evaluate_garbled_circuit(&circuit, &prover_labels);
        let output_hash = crate::garbled::hash_label(&eval.output_label);
        #[allow(deprecated)]
        let air =
            GarbledEvaluationAir::new(eval.gate_trace, circuit.circuit_commitment, output_hash);
        ConstraintAir::generate_trace(&air)
    }

    #[test]
    fn p3_garbled_prove_verify_roundtrips() {
        let (trace, pis) = real_trace();
        assert_eq!(trace[0].len(), GARBLED_EVAL_AIR_WIDTH);
        let proof = prove_garbled_p3(&trace, &pis);
        verify_garbled_p3(&proof, &pis).expect("honest garbled proof must verify");
    }

    #[test]
    fn p3_garbled_wrong_public_input_rejected() {
        let (trace, pis) = real_trace();
        let proof = prove_garbled_p3(&trace, &pis);
        // Flip the claimed circuit_commitment[0]; the trace cell no longer matches.
        let mut wrong = pis.clone();
        wrong[0] = wrong[0] + BabyBear::ONE;
        let result = verify_garbled_p3(&proof, &wrong);
        assert!(result.is_err(), "wrong public input MUST be rejected");
    }

    /// Soundness: forge a decrypted output label without fixing the
    /// (table_entry - hash_out) identity. In release the prover produces a proof
    /// whose constraints are violated; verify must reject. In debug the p3 prover
    /// panics on the violated trace before producing a proof (matches the
    /// `plonky3_forged_parent_rejected` convention), so gate on release.
    #[test]
    #[cfg(not(debug_assertions))]
    fn p3_garbled_forged_output_label_rejected() {
        let (mut trace, pis) = real_trace();
        // Corrupt output[0] on row 0 so output != table_entry - hash_out.
        trace[0][col::output(0)] = trace[0][col::output(0)] + BabyBear::ONE;
        let proof = prove_garbled_p3(&trace, &pis);
        let result = verify_garbled_p3(&proof, &pis);
        assert!(
            result.is_err(),
            "forged output label MUST be rejected by the decryption-correctness constraint"
        );
    }
}
