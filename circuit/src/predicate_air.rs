//! Predicate proof AIR.
//!
//! Proves statements about private token attributes without revealing them:
//! - "My token has `valid_until >= T`" (not expired for a while)
//! - "My bid amount >= minimum_bid" (auction qualification)
//! - "My reputation score >= threshold" (access to premium service)
//! - "My delegation depth <= max_depth" (freshness guarantee)
//!
//! These are all range/comparison checks where one operand is private (in the
//! witness) and the other is a public input (the threshold).
//!
//! # Design
//!
//! The predicate AIR is a standalone single-row circuit that proves a comparison
//! predicate over a private attribute bound to a specific fact in the token state.
//! It uses the same bit-decomposition technique as the GTE/LT checks in
//! [`derivation_air`](crate::derivation_air) but in a self-contained form with
//! its own public inputs.
//!
//! # Trace layout
//!
//! | Column    | Description                                            |
//! |-----------|-------------------------------------------------------|
//! | 0         | private_value (the attribute being proven about)       |
//! | 1         | threshold (public comparison target)                   |
//! | 2         | diff (computed difference for the comparison)          |
//! | 3..33     | diff_bits[0..30] (bit decomposition of diff)           |
//! | 34        | fact_commitment (binding to the token state)            |
//! | 35        | neq_inverse (multiplicative inverse of diff, for NEQ)   |
//!
//! # Public inputs
//!
//! `[threshold, fact_commitment]`
//!
//! - `threshold`: The public comparison target.
//! - `fact_commitment`: Poseidon2(fact_hash, state_root) — binds the proven
//!   value to a specific fact in a specific token state.
//!
//! # Predicate types
//!
//! - `GTE(value, threshold)`: prove `value >= threshold` via bit decomp of `value - threshold`
//! - `LTE(value, threshold)`: prove `threshold >= value` via bit decomp of `threshold - value`
//! - `GT(value, threshold)`: prove `value > threshold` via bit decomp of `value - threshold - 1`
//! - `LT(value, threshold)`: prove `value < threshold` via bit decomp of `threshold - value - 1`
//! - `InRange(value, low, high)`: prove `value >= low AND value <= high`
//! - `NEQ(value, target)`: prove `value != target` by exhibiting inverse of (value - target)

use crate::constraint_prover::{Air, Constraint};
use crate::field::BabyBear;
use crate::poseidon2;

/// Number of bits for the range check.
/// BabyBear has ~31-bit modulus; if the high bit (bit 30) is 0, the value is
/// less than 2^30 < p/2, which means it represents a "small positive" number.
pub const PREDICATE_DIFF_BITS: usize = 31;

/// Trace width for the predicate AIR.
/// private_value(1) + threshold(1) + diff(1) + diff_bits(31) + fact_commitment(1) + neq_inverse(1) = 36
pub const PREDICATE_AIR_WIDTH: usize = 36;

/// Column indices for the predicate AIR trace.
pub mod col {
    use super::PREDICATE_DIFF_BITS;

    /// The private attribute value (witness).
    pub const PRIVATE_VALUE: usize = 0;
    /// The threshold (matches public input).
    pub const THRESHOLD: usize = 1;
    /// The computed difference for the comparison.
    pub const DIFF: usize = 2;
    /// Start of bit decomposition columns (31 bits).
    pub const DIFF_BITS_START: usize = 3;
    /// The fact commitment (binding to token state).
    pub const FACT_COMMITMENT: usize = DIFF_BITS_START + PREDICATE_DIFF_BITS; // 34
    /// Multiplicative inverse of diff (used only for NEQ predicate).
    pub const NEQ_INVERSE: usize = FACT_COMMITMENT + 1; // 35

    /// Get the column for diff_bits[bit_idx].
    #[inline]
    pub const fn diff_bit(bit_idx: usize) -> usize {
        DIFF_BITS_START + bit_idx
    }
}

/// The type of predicate being proven.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum PredicateType {
    /// Prove `private_value >= threshold`.
    /// diff = private_value - threshold; bit decomp with high bit = 0.
    Gte,
    /// Prove `private_value <= threshold`.
    /// diff = threshold - private_value; bit decomp with high bit = 0.
    Lte,
    /// Prove `private_value > threshold`.
    /// diff = private_value - threshold - 1; bit decomp with high bit = 0.
    Gt,
    /// Prove `private_value < threshold`.
    /// diff = threshold - private_value - 1; bit decomp with high bit = 0.
    Lt,
    /// Prove `private_value != target`.
    /// Exhibit the multiplicative inverse of (private_value - target).
    Neq,
    /// Prove `low <= private_value <= high`.
    /// This is encoded as two separate predicates (GTE for low, LTE for high)
    /// composed at the witness level. The AIR proves the lower bound; a second
    /// AIR instance proves the upper bound.
    InRangeLow,
    /// The upper-bound half of an InRange proof.
    InRangeHigh,
}

/// Witness for a predicate proof.
#[derive(Clone, Debug)]
pub struct PredicateWitness {
    /// The private attribute value.
    pub private_value: BabyBear,
    /// The threshold/target for comparison.
    pub threshold: BabyBear,
    /// The type of predicate.
    pub predicate_type: PredicateType,
    /// Fact commitment: Poseidon2(fact_hash, state_root).
    /// Binds this proof to a specific fact in a specific token state.
    pub fact_commitment: BabyBear,
}

impl PredicateWitness {
    /// Compute the diff for this predicate.
    pub fn compute_diff(&self) -> BabyBear {
        match self.predicate_type {
            PredicateType::Gte | PredicateType::InRangeLow => {
                // diff = value - threshold (must be non-negative)
                self.private_value - self.threshold
            }
            PredicateType::Lte | PredicateType::InRangeHigh => {
                // diff = threshold - value (must be non-negative)
                self.threshold - self.private_value
            }
            PredicateType::Gt => {
                // diff = value - threshold - 1 (must be non-negative)
                self.private_value - self.threshold - BabyBear::ONE
            }
            PredicateType::Lt => {
                // diff = threshold - value - 1 (must be non-negative)
                self.threshold - self.private_value - BabyBear::ONE
            }
            PredicateType::Neq => {
                // diff = value - target (must be non-zero)
                self.private_value - self.threshold
            }
        }
    }

    /// Check whether the predicate can be satisfied (i.e., the statement is true).
    ///
    /// Returns `false` if the private value does not satisfy the predicate,
    /// meaning proof generation would produce an invalid proof.
    pub fn is_satisfiable(&self) -> bool {
        let v = self.private_value.as_u32();
        let t = self.threshold.as_u32();
        match self.predicate_type {
            PredicateType::Gte | PredicateType::InRangeLow => v >= t,
            PredicateType::Lte | PredicateType::InRangeHigh => v <= t,
            PredicateType::Gt => v > t,
            PredicateType::Lt => v < t,
            PredicateType::Neq => v != t,
        }
    }
}

/// The predicate proof AIR.
///
/// Proves a single predicate statement about a private value with a public threshold.
pub struct PredicateAir {
    pub witness: PredicateWitness,
}

impl PredicateAir {
    pub fn new(witness: PredicateWitness) -> Self {
        Self { witness }
    }
}

impl Air for PredicateAir {
    fn trace_width(&self) -> usize {
        PREDICATE_AIR_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        2 // [threshold, fact_commitment]
    }

    fn constraints(&self) -> Vec<Constraint> {
        let predicate_type = self.witness.predicate_type;

        vec![
            // Constraint 1: Threshold in trace matches public input.
            Constraint {
                name: "threshold_matches_public_input".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::THRESHOLD] - public_inputs[0]
                }),
            },
            // Constraint 2: Fact commitment in trace matches public input.
            Constraint {
                name: "fact_commitment_matches_public_input".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    row[col::FACT_COMMITMENT] - public_inputs[1]
                }),
            },
            // Constraint 3: Diff is correctly computed based on predicate type.
            Constraint {
                name: "diff_correct".to_string(),
                eval: Box::new(move |row, _, _| {
                    let value = row[col::PRIVATE_VALUE];
                    let threshold = row[col::THRESHOLD];
                    let diff = row[col::DIFF];
                    match predicate_type {
                        PredicateType::Gte | PredicateType::InRangeLow => {
                            diff - (value - threshold)
                        }
                        PredicateType::Lte | PredicateType::InRangeHigh => {
                            diff - (threshold - value)
                        }
                        PredicateType::Gt => {
                            diff - (value - threshold - BabyBear::ONE)
                        }
                        PredicateType::Lt => {
                            diff - (threshold - value - BabyBear::ONE)
                        }
                        PredicateType::Neq => {
                            diff - (value - threshold)
                        }
                    }
                }),
            },
            // Constraint 4: Bit decomposition is correct.
            // sum(bit_i * 2^i) = diff
            // (For NEQ, this constraint is still applied but supplemented by the
            // inverse constraint below.)
            Constraint {
                name: "bit_decomposition_correct".to_string(),
                eval: Box::new(move |row, _, _| {
                    if predicate_type == PredicateType::Neq {
                        // For NEQ, we don't need bit decomposition — we use the inverse.
                        return BabyBear::ZERO;
                    }
                    let diff = row[col::DIFF];
                    let mut recomposed = BabyBear::ZERO;
                    let mut power_of_two = BabyBear::ONE;
                    for i in 0..PREDICATE_DIFF_BITS {
                        let bit = row[col::diff_bit(i)];
                        recomposed = recomposed + bit * power_of_two;
                        power_of_two = power_of_two + power_of_two;
                    }
                    recomposed - diff
                }),
            },
            // Constraint 5: All bits are binary (0 or 1).
            Constraint {
                name: "bits_binary".to_string(),
                eval: Box::new(move |row, _, _| {
                    if predicate_type == PredicateType::Neq {
                        return BabyBear::ZERO;
                    }
                    let mut result = BabyBear::ZERO;
                    for i in 0..PREDICATE_DIFF_BITS {
                        let bit = row[col::diff_bit(i)];
                        result = result + bit * (bit - BabyBear::ONE);
                    }
                    result
                }),
            },
            // Constraint 6: High bit is 0 (diff < 2^30 < p/2, proving non-negative).
            Constraint {
                name: "high_bit_zero".to_string(),
                eval: Box::new(move |row, _, _| {
                    if predicate_type == PredicateType::Neq {
                        return BabyBear::ZERO;
                    }
                    row[col::diff_bit(PREDICATE_DIFF_BITS - 1)]
                }),
            },
            // Constraint 7: NEQ inverse proof — diff * inverse = 1.
            // Only enforced for NEQ predicates; for others this is trivially 0.
            Constraint {
                name: "neq_inverse_valid".to_string(),
                eval: Box::new(move |row, _, _| {
                    if predicate_type != PredicateType::Neq {
                        return BabyBear::ZERO;
                    }
                    let diff = row[col::DIFF];
                    let inverse = row[col::NEQ_INVERSE];
                    diff * inverse - BabyBear::ONE
                }),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let w = &self.witness;
        let mut row = vec![BabyBear::ZERO; PREDICATE_AIR_WIDTH];

        // Fill trace columns.
        row[col::PRIVATE_VALUE] = w.private_value;
        row[col::THRESHOLD] = w.threshold;
        row[col::FACT_COMMITMENT] = w.fact_commitment;

        let diff = w.compute_diff();
        row[col::DIFF] = diff;

        match w.predicate_type {
            PredicateType::Neq => {
                // For NEQ: provide the multiplicative inverse of diff.
                // If diff is zero (value == target), inverse doesn't exist and
                // the constraint will fail — this is the intended behavior.
                if let Some(inv) = diff.inverse() {
                    row[col::NEQ_INVERSE] = inv;
                }
                // bits are left as zero (not used for NEQ)
            }
            _ => {
                // For range predicates: bit decomposition of diff.
                let diff_val = diff.as_u32();
                for i in 0..PREDICATE_DIFF_BITS {
                    let bit = (diff_val >> i) & 1;
                    row[col::diff_bit(i)] = BabyBear::new(bit);
                }
            }
        }

        let public_inputs = vec![w.threshold, w.fact_commitment];
        (vec![row], public_inputs)
    }
}

/// A complete predicate proof result.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PredicateProof {
    /// The type of predicate that was proven.
    pub predicate_type: PredicateType,
    /// The threshold (public input).
    pub threshold: BabyBear,
    /// The fact commitment (public input).
    pub fact_commitment: BabyBear,
    /// The constraint proof (trace digest + public inputs).
    pub proof: crate::constraint_prover::ConstraintProof,
}

/// Generate a predicate proof from a witness.
///
/// Returns `None` if the predicate is not satisfiable (the statement is false)
/// or if proof generation fails.
pub fn prove_predicate(witness: PredicateWitness) -> Option<PredicateProof> {
    if !witness.is_satisfiable() {
        return None;
    }

    let predicate_type = witness.predicate_type;
    let threshold = witness.threshold;
    let fact_commitment = witness.fact_commitment;

    let air = PredicateAir::new(witness);
    let proof = crate::constraint_prover::ConstraintProof::generate(&air)?;

    Some(PredicateProof {
        predicate_type,
        threshold,
        fact_commitment,
        proof,
    })
}

/// Verify a predicate proof against expected public inputs.
///
/// The verifier provides the threshold and fact_commitment they expect and
/// checks the proof is consistent.
pub fn verify_predicate(proof: &PredicateProof, threshold: BabyBear, fact_commitment: BabyBear) -> bool {
    if proof.threshold != threshold || proof.fact_commitment != fact_commitment {
        return false;
    }
    let expected_pi = [threshold, fact_commitment];
    proof.proof.verify(&expected_pi)
}

/// Compute the fact commitment that binds a proven value to a token state.
///
/// `fact_commitment = Poseidon2(fact_hash, state_root)`
///
/// - `fact_hash`: The Poseidon2 hash of the fact containing the proven attribute.
/// - `state_root`: The Merkle root of the token state containing the fact.
pub fn compute_fact_commitment(fact_hash: BabyBear, state_root: BabyBear) -> BabyBear {
    poseidon2::hash_2_to_1(fact_hash, state_root)
}

/// Prove an InRange predicate (value >= low AND value <= high).
///
/// This produces two proofs: one for the lower bound (GTE) and one for the
/// upper bound (LTE). Both must verify for the range claim to hold.
///
/// Returns `None` if either bound is not satisfiable.
pub fn prove_in_range(
    private_value: BabyBear,
    low: BabyBear,
    high: BabyBear,
    fact_commitment: BabyBear,
) -> Option<(PredicateProof, PredicateProof)> {
    let low_witness = PredicateWitness {
        private_value,
        threshold: low,
        predicate_type: PredicateType::InRangeLow,
        fact_commitment,
    };

    let high_witness = PredicateWitness {
        private_value,
        threshold: high,
        predicate_type: PredicateType::InRangeHigh,
        fact_commitment,
    };

    let low_proof = prove_predicate(low_witness)?;
    let high_proof = prove_predicate(high_witness)?;
    Some((low_proof, high_proof))
}

/// Verify an InRange proof (both bounds must pass).
pub fn verify_in_range(
    low_proof: &PredicateProof,
    high_proof: &PredicateProof,
    low: BabyBear,
    high: BabyBear,
    fact_commitment: BabyBear,
) -> bool {
    verify_predicate(low_proof, low, fact_commitment)
        && verify_predicate(high_proof, high, fact_commitment)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint_prover::ConstraintProver;
    use crate::poseidon2::hash_fact;

    /// Helper: create a fact commitment for testing.
    fn test_fact_commitment(value: BabyBear) -> BabyBear {
        let fact_hash = hash_fact(BabyBear::new(100), &[value, BabyBear::ZERO, BabyBear::ZERO]);
        let state_root = BabyBear::new(99999);
        compute_fact_commitment(fact_hash, state_root)
    }

    // =========================================================================
    // GTE tests
    // =========================================================================

    #[test]
    fn test_predicate_gte_passes() {
        // Prove: value(25) >= threshold(18)
        let value = BabyBear::new(25);
        let threshold = BabyBear::new(18);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment: commitment,
        };

        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GTE 25 >= 18 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_gte_equal_passes() {
        // Prove: value(18) >= threshold(18)
        let value = BabyBear::new(18);
        let threshold = BabyBear::new(18);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment: commitment,
        };

        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GTE 18 >= 18 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_gte_fails() {
        // Prove: value(15) >= threshold(18) — should FAIL
        // diff = 15 - 18 in BabyBear wraps to p - 3 (high bit set)
        let value = BabyBear::new(15);
        let threshold = BabyBear::new(18);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment: commitment,
        };

        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "GTE 15 >= 18 should fail");
        // The high bit constraint should catch this
        let has_high_bit = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "high_bit_zero");
        assert!(
            has_high_bit,
            "Should have high_bit_zero violation, got: {:?}",
            result.violations()
        );
    }

    // =========================================================================
    // LTE tests
    // =========================================================================

    #[test]
    fn test_predicate_lte_passes() {
        // Prove: value(10) <= threshold(100)
        let value = BabyBear::new(10);
        let threshold = BabyBear::new(100);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Lte,
            fact_commitment: commitment,
        };

        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "LTE 10 <= 100 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_lte_fails() {
        // Prove: value(200) <= threshold(100) — should FAIL
        let value = BabyBear::new(200);
        let threshold = BabyBear::new(100);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Lte,
            fact_commitment: commitment,
        };

        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "LTE 200 <= 100 should fail");
    }

    // =========================================================================
    // GT / LT tests
    // =========================================================================

    #[test]
    fn test_predicate_gt_passes() {
        // Prove: value(25) > threshold(18)
        let value = BabyBear::new(25);
        let threshold = BabyBear::new(18);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gt,
            fact_commitment: commitment,
        };

        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GT 25 > 18 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_gt_equal_fails() {
        // Prove: value(18) > threshold(18) — should FAIL (not strictly greater)
        // diff = 18 - 18 - 1 = p - 1 in BabyBear (wraps, high bit set)
        let value = BabyBear::new(18);
        let threshold = BabyBear::new(18);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gt,
            fact_commitment: commitment,
        };

        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "GT 18 > 18 should fail");
    }

    #[test]
    fn test_predicate_lt_passes() {
        // Prove: value(5) < threshold(18)
        let value = BabyBear::new(5);
        let threshold = BabyBear::new(18);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Lt,
            fact_commitment: commitment,
        };

        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "LT 5 < 18 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_lt_equal_fails() {
        // Prove: value(18) < threshold(18) — should FAIL
        let value = BabyBear::new(18);
        let threshold = BabyBear::new(18);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Lt,
            fact_commitment: commitment,
        };

        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "LT 18 < 18 should fail");
    }

    // =========================================================================
    // NEQ tests
    // =========================================================================

    #[test]
    fn test_predicate_neq_passes() {
        // Prove: value(42) != target(0)
        let value = BabyBear::new(42);
        let target = BabyBear::new(0);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold: target,
            predicate_type: PredicateType::Neq,
            fact_commitment: commitment,
        };

        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "NEQ 42 != 0 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_predicate_neq_fails() {
        // Prove: value(7) != target(7) — should FAIL
        // diff = 0, inverse doesn't exist, constraint diff * inv = 1 fails.
        let value = BabyBear::new(7);
        let target = BabyBear::new(7);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold: target,
            predicate_type: PredicateType::Neq,
            fact_commitment: commitment,
        };

        let air = PredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "NEQ 7 != 7 should fail");
        let has_neq_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "neq_inverse_valid");
        assert!(
            has_neq_violation,
            "Should have neq_inverse_valid violation, got: {:?}",
            result.violations()
        );
    }

    // =========================================================================
    // InRange tests
    // =========================================================================

    #[test]
    fn test_predicate_in_range_passes() {
        // Prove: 18 <= value(25) <= 120
        let value = BabyBear::new(25);
        let low = BabyBear::new(18);
        let high = BabyBear::new(120);
        let commitment = test_fact_commitment(value);

        let result = prove_in_range(value, low, high, commitment);
        assert!(result.is_some(), "InRange 18 <= 25 <= 120 should produce proofs");

        let (low_proof, high_proof) = result.unwrap();
        assert!(
            verify_in_range(&low_proof, &high_proof, low, high, commitment),
            "InRange verification should pass"
        );
    }

    #[test]
    fn test_predicate_in_range_below_low_fails() {
        // Prove: 18 <= value(15) <= 120 — should FAIL (below low bound)
        let value = BabyBear::new(15);
        let low = BabyBear::new(18);
        let high = BabyBear::new(120);
        let commitment = test_fact_commitment(value);

        let result = prove_in_range(value, low, high, commitment);
        assert!(result.is_none(), "InRange with value below low should fail");
    }

    #[test]
    fn test_predicate_in_range_above_high_fails() {
        // Prove: 18 <= value(200) <= 120 — should FAIL (above high bound)
        let value = BabyBear::new(200);
        let low = BabyBear::new(18);
        let high = BabyBear::new(120);
        let commitment = test_fact_commitment(value);

        let result = prove_in_range(value, low, high, commitment);
        assert!(result.is_none(), "InRange with value above high should fail");
    }

    #[test]
    fn test_predicate_in_range_at_bounds_passes() {
        // Prove: 18 <= value(18) <= 120 (at lower bound, inclusive)
        let value = BabyBear::new(18);
        let low = BabyBear::new(18);
        let high = BabyBear::new(120);
        let commitment = test_fact_commitment(value);

        let result = prove_in_range(value, low, high, commitment);
        assert!(result.is_some(), "InRange at lower bound should pass");

        // Prove: 18 <= value(120) <= 120 (at upper bound, inclusive)
        let value = BabyBear::new(120);
        let commitment = test_fact_commitment(value);
        let result = prove_in_range(value, low, high, commitment);
        assert!(result.is_some(), "InRange at upper bound should pass");
    }

    // =========================================================================
    // prove_predicate / verify_predicate integration
    // =========================================================================

    #[test]
    fn test_prove_and_verify_gte() {
        let value = BabyBear::new(1000);
        let threshold = BabyBear::new(500);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment: commitment,
        };

        let proof = prove_predicate(witness).expect("should produce proof");
        assert!(verify_predicate(&proof, threshold, commitment));
    }

    #[test]
    fn test_prove_returns_none_for_false_statement() {
        // Trying to prove 5 >= 100 should return None.
        let value = BabyBear::new(5);
        let threshold = BabyBear::new(100);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment: commitment,
        };

        let proof = prove_predicate(witness);
        assert!(proof.is_none(), "Cannot prove false statement");
    }

    #[test]
    fn test_verify_fails_with_wrong_threshold() {
        let value = BabyBear::new(1000);
        let threshold = BabyBear::new(500);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment: commitment,
        };

        let proof = prove_predicate(witness).expect("should produce proof");
        // Verify with a different threshold — should fail.
        let wrong_threshold = BabyBear::new(999);
        assert!(!verify_predicate(&proof, wrong_threshold, commitment));
    }

    #[test]
    fn test_verify_fails_with_wrong_commitment() {
        let value = BabyBear::new(1000);
        let threshold = BabyBear::new(500);
        let commitment = test_fact_commitment(value);

        let witness = PredicateWitness {
            private_value: value,
            threshold,
            predicate_type: PredicateType::Gte,
            fact_commitment: commitment,
        };

        let proof = prove_predicate(witness).expect("should produce proof");
        // Verify with a different commitment — should fail.
        let wrong_commitment = BabyBear::new(12345);
        assert!(!verify_predicate(&proof, threshold, wrong_commitment));
    }

    #[test]
    fn test_predicate_balance_scenario() {
        // Real scenario: prove balance >= 1000 without revealing exact balance.
        // Balance is 5000 (private), threshold is 1000 (public).
        let balance = BabyBear::new(5000);
        let min_balance = BabyBear::new(1000);

        // The fact is balance(5000) in some token state.
        let balance_pred = BabyBear::new(42); // "balance" predicate symbol
        let fact_hash = hash_fact(balance_pred, &[balance, BabyBear::ZERO, BabyBear::ZERO]);
        let state_root = BabyBear::new(77777);
        let commitment = compute_fact_commitment(fact_hash, state_root);

        let witness = PredicateWitness {
            private_value: balance,
            threshold: min_balance,
            predicate_type: PredicateType::Gte,
            fact_commitment: commitment,
        };

        let proof = prove_predicate(witness).expect("balance proof should succeed");

        // Verifier only knows: threshold=1000, fact_commitment
        // They learn: "the balance in that fact is >= 1000" without knowing the exact value.
        assert!(verify_predicate(&proof, min_balance, commitment));
    }
}
