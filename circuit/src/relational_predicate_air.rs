//! Relational predicate AIR: two-party value comparison without revealing either value.
//!
//! Proves statements comparing two private values, each bound to a Poseidon2 commitment:
//! - "Prove my_value > their_value" (auction winner determination)
//! - "Prove my_value < their_value" (reverse comparison)
//! - "Prove my_value == their_value" (equality)
//! - "Prove my_value != their_value" (inequality)
//! - "Prove my_value - their_value > threshold" (relative standing)
//! - "Prove my_value + their_value > threshold" (joint qualification)
//!
//! # Protocol (Delegated Comparison with Sealed Values)
//!
//! 1. Alice commits: `C_a = Poseidon2(value_a, blinding_a)` -- publishes C_a
//! 2. Bob commits: `C_b = Poseidon2(value_b, blinding_b)` -- publishes C_b
//! 3. A comparison service (or trusted third party) receives both values + blindings
//! 4. The service generates a STARK proof proving:
//!    - `Poseidon2(value_a, blinding_a) == C_a` (commitment binding)
//!    - `Poseidon2(value_b, blinding_b) == C_b` (commitment binding)
//!    - The claimed relation holds between value_a and value_b
//! 5. Public inputs: `[C_a, C_b, result_bit]`
//! 6. Anyone can verify the proof; neither value is revealed.
//!
//! # Security
//!
//! - The PROVER knows both values (it is the comparison service).
//! - Neither Alice nor Bob learns the other's value.
//! - VERIFIERS (third parties) learn only that the relation holds, plus the commitments.
//! - The commitment scheme (Poseidon2) provides binding: values cannot be changed post-commit.
//! - Different blindings make commitments unlinkable across sessions.
//!
//! # Trace Layout (width = 38)
//!
//! | Columns   | Description                                      |
//! |-----------|--------------------------------------------------|
//! | 0         | value_a (private witness)                        |
//! | 1         | blinding_a (private witness)                     |
//! | 2         | value_b (private witness)                        |
//! | 3         | blinding_b (private witness)                     |
//! | 4         | diff = f(value_a, value_b) per relation type     |
//! | 5..36     | diff_bits[0..31] (bit decomposition for range)   |
//! | 36        | neq_inverse (for NEQ relation only)              |
//! | 37        | result_bit (1 if relation holds, 0 otherwise)    |
//!
//! # Public Inputs
//!
//! `[commitment_a, commitment_b, result_bit]`
//!
//! - `commitment_a`: Poseidon2(value_a, blinding_a) -- Alice's commitment
//! - `commitment_b`: Poseidon2(value_b, blinding_b) -- Bob's commitment
//! - `result_bit`: 1 if the relation holds, 0 if not (always 1 for a valid proof)

use crate::constraint_prover::{Air, Constraint};
use crate::field::BabyBear;
use crate::poseidon2;

/// Number of bits for the range check (same as predicate_air).
pub const RELATIONAL_DIFF_BITS: usize = 31;

/// Trace width for the relational predicate AIR.
/// value_a(1) + blinding_a(1) + value_b(1) + blinding_b(1) + diff(1)
/// + diff_bits(31) + neq_inverse(1) + result_bit(1) = 38
pub const RELATIONAL_AIR_WIDTH: usize = 38;

/// Column indices for the relational predicate AIR trace.
pub mod col {
    use super::RELATIONAL_DIFF_BITS;

    /// Value A (private witness from Alice).
    pub const VALUE_A: usize = 0;
    /// Blinding factor for commitment A (private witness).
    pub const BLINDING_A: usize = 1;
    /// Value B (private witness from Bob).
    pub const VALUE_B: usize = 2;
    /// Blinding factor for commitment B (private witness).
    pub const BLINDING_B: usize = 3;
    /// Computed difference for the comparison.
    pub const DIFF: usize = 4;
    /// Start of bit decomposition columns (31 bits).
    pub const DIFF_BITS_START: usize = 5;
    /// Multiplicative inverse of diff (used only for NEQ relation).
    pub const NEQ_INVERSE: usize = DIFF_BITS_START + RELATIONAL_DIFF_BITS; // 36
    /// Result bit (1 = relation holds). Always 1 for a valid proof.
    pub const RESULT_BIT: usize = NEQ_INVERSE + 1; // 37

    /// Get the column for diff_bits[bit_idx].
    #[inline]
    pub const fn diff_bit(bit_idx: usize) -> usize {
        DIFF_BITS_START + bit_idx
    }
}

/// The type of relational comparison being proven.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelationType {
    /// Prove `value_a > value_b`.
    /// diff = value_a - value_b - 1; bit decomp with high bit = 0.
    GreaterThan,
    /// Prove `value_a < value_b`.
    /// diff = value_b - value_a - 1; bit decomp with high bit = 0.
    LessThan,
    /// Prove `value_a >= value_b`.
    /// diff = value_a - value_b; bit decomp with high bit = 0.
    GreaterOrEqual,
    /// Prove `value_a <= value_b`.
    /// diff = value_b - value_a; bit decomp with high bit = 0.
    LessOrEqual,
    /// Prove `value_a == value_b`.
    /// diff = value_a - value_b; must be zero.
    Equal,
    /// Prove `value_a != value_b`.
    /// diff = value_a - value_b; exhibit multiplicative inverse.
    NotEqual,
    /// Prove `value_a - value_b > threshold`.
    /// diff = value_a - value_b - threshold - 1; bit decomp with high bit = 0.
    DiffGreaterThan(BabyBear),
    /// Prove `value_a + value_b > threshold`.
    /// diff = value_a + value_b - threshold - 1; bit decomp with high bit = 0.
    SumGreaterThan(BabyBear),
}

/// Witness for a relational predicate proof.
#[derive(Clone, Debug)]
pub struct RelationalPredicateWitness {
    /// Alice's private value.
    pub value_a: BabyBear,
    /// Alice's blinding factor for her commitment.
    pub blinding_a: BabyBear,
    /// Bob's private value.
    pub value_b: BabyBear,
    /// Bob's blinding factor for his commitment.
    pub blinding_b: BabyBear,
    /// The type of relation to prove.
    pub relation: RelationType,
}

impl RelationalPredicateWitness {
    /// Compute the commitment for value A: Poseidon2(value_a, blinding_a).
    pub fn commitment_a(&self) -> BabyBear {
        compute_value_commitment(self.value_a, self.blinding_a)
    }

    /// Compute the commitment for value B: Poseidon2(value_b, blinding_b).
    pub fn commitment_b(&self) -> BabyBear {
        compute_value_commitment(self.value_b, self.blinding_b)
    }

    /// Compute the diff for this relation.
    pub fn compute_diff(&self) -> BabyBear {
        match self.relation {
            RelationType::GreaterThan => {
                // diff = a - b - 1 (must be non-negative for a > b)
                self.value_a - self.value_b - BabyBear::ONE
            }
            RelationType::LessThan => {
                // diff = b - a - 1 (must be non-negative for a < b)
                self.value_b - self.value_a - BabyBear::ONE
            }
            RelationType::GreaterOrEqual => {
                // diff = a - b (must be non-negative for a >= b)
                self.value_a - self.value_b
            }
            RelationType::LessOrEqual => {
                // diff = b - a (must be non-negative for a <= b)
                self.value_b - self.value_a
            }
            RelationType::Equal | RelationType::NotEqual => {
                // diff = a - b
                self.value_a - self.value_b
            }
            RelationType::DiffGreaterThan(threshold) => {
                // diff = (a - b) - threshold - 1 (must be non-negative)
                self.value_a - self.value_b - threshold - BabyBear::ONE
            }
            RelationType::SumGreaterThan(threshold) => {
                // diff = (a + b) - threshold - 1 (must be non-negative)
                self.value_a + self.value_b - threshold - BabyBear::ONE
            }
        }
    }

    /// Check whether the relation is satisfiable (the statement is actually true).
    ///
    /// Returns `false` if the values do not satisfy the relation.
    pub fn is_satisfiable(&self) -> bool {
        let a = self.value_a.as_u32();
        let b = self.value_b.as_u32();
        match self.relation {
            RelationType::GreaterThan => a > b,
            RelationType::LessThan => a < b,
            RelationType::GreaterOrEqual => a >= b,
            RelationType::LessOrEqual => a <= b,
            RelationType::Equal => a == b,
            RelationType::NotEqual => a != b,
            RelationType::DiffGreaterThan(threshold) => {
                // a - b > threshold (all as u32, check for underflow)
                a > b && (a - b) > threshold.as_u32()
            }
            RelationType::SumGreaterThan(threshold) => {
                // a + b > threshold
                (a as u64 + b as u64) > threshold.as_u32() as u64
            }
        }
    }
}

/// The relational predicate AIR.
///
/// Proves a comparison between two private values, each bound to a public commitment.
pub struct RelationalPredicateAir {
    pub witness: RelationalPredicateWitness,
}

impl RelationalPredicateAir {
    pub fn new(witness: RelationalPredicateWitness) -> Self {
        Self { witness }
    }
}

impl Air for RelationalPredicateAir {
    fn trace_width(&self) -> usize {
        RELATIONAL_AIR_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        3 // [commitment_a, commitment_b, result_bit]
    }

    fn constraints(&self) -> Vec<Constraint> {
        let relation = self.witness.relation;

        vec![
            // Constraint 1: Commitment A is correctly computed.
            // Poseidon2(value_a, blinding_a) must match public input commitment_a.
            Constraint {
                name: "commitment_a_binding".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    let value_a = row[col::VALUE_A];
                    let blinding_a = row[col::BLINDING_A];
                    let expected = compute_value_commitment(value_a, blinding_a);
                    expected - public_inputs[0]
                }),
            },
            // Constraint 2: Commitment B is correctly computed.
            // Poseidon2(value_b, blinding_b) must match public input commitment_b.
            Constraint {
                name: "commitment_b_binding".to_string(),
                eval: Box::new(|row, _, public_inputs| {
                    let value_b = row[col::VALUE_B];
                    let blinding_b = row[col::BLINDING_B];
                    let expected = compute_value_commitment(value_b, blinding_b);
                    expected - public_inputs[1]
                }),
            },
            // Constraint 3: Diff is correctly computed based on relation type.
            Constraint {
                name: "diff_correct".to_string(),
                eval: Box::new(move |row, _, _| {
                    let value_a = row[col::VALUE_A];
                    let value_b = row[col::VALUE_B];
                    let diff = row[col::DIFF];
                    match relation {
                        RelationType::GreaterThan => diff - (value_a - value_b - BabyBear::ONE),
                        RelationType::LessThan => diff - (value_b - value_a - BabyBear::ONE),
                        RelationType::GreaterOrEqual => diff - (value_a - value_b),
                        RelationType::LessOrEqual => diff - (value_b - value_a),
                        RelationType::Equal | RelationType::NotEqual => diff - (value_a - value_b),
                        RelationType::DiffGreaterThan(threshold) => {
                            diff - (value_a - value_b - threshold - BabyBear::ONE)
                        }
                        RelationType::SumGreaterThan(threshold) => {
                            diff - (value_a + value_b - threshold - BabyBear::ONE)
                        }
                    }
                }),
            },
            // Constraint 4: Bit decomposition is correct (for range-based relations).
            Constraint {
                name: "bit_decomposition_correct".to_string(),
                eval: Box::new(move |row, _, _| {
                    // For Equal: diff must be zero (no bit decomp needed).
                    // For NotEqual: inverse proof (no bit decomp needed).
                    if matches!(relation, RelationType::Equal | RelationType::NotEqual) {
                        return BabyBear::ZERO;
                    }
                    let diff = row[col::DIFF];
                    let mut recomposed = BabyBear::ZERO;
                    let mut power_of_two = BabyBear::ONE;
                    for i in 0..RELATIONAL_DIFF_BITS {
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
                    if matches!(relation, RelationType::Equal | RelationType::NotEqual) {
                        return BabyBear::ZERO;
                    }
                    let mut result = BabyBear::ZERO;
                    for i in 0..RELATIONAL_DIFF_BITS {
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
                    if matches!(relation, RelationType::Equal | RelationType::NotEqual) {
                        return BabyBear::ZERO;
                    }
                    row[col::diff_bit(RELATIONAL_DIFF_BITS - 1)]
                }),
            },
            // Constraint 7: For Equal, diff must be zero.
            Constraint {
                name: "equal_diff_zero".to_string(),
                eval: Box::new(move |row, _, _| {
                    if relation != RelationType::Equal {
                        return BabyBear::ZERO;
                    }
                    row[col::DIFF]
                }),
            },
            // Constraint 8: For NotEqual, diff * inverse = 1.
            Constraint {
                name: "neq_inverse_valid".to_string(),
                eval: Box::new(move |row, _, _| {
                    if relation != RelationType::NotEqual {
                        return BabyBear::ZERO;
                    }
                    let diff = row[col::DIFF];
                    let inverse = row[col::NEQ_INVERSE];
                    diff * inverse - BabyBear::ONE
                }),
            },
            // Constraint 9: Result bit matches public input and is 1.
            // (A valid proof always has result_bit = 1.)
            Constraint {
                name: "result_bit_matches_pi".to_string(),
                eval: Box::new(|row, _, public_inputs| row[col::RESULT_BIT] - public_inputs[2]),
            },
            // Constraint 10: Result bit is 1 (proof only valid if relation holds).
            Constraint {
                name: "result_bit_is_one".to_string(),
                eval: Box::new(|row, _, _| row[col::RESULT_BIT] - BabyBear::ONE),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let w = &self.witness;
        let mut row = vec![BabyBear::ZERO; RELATIONAL_AIR_WIDTH];

        // Fill witness columns.
        row[col::VALUE_A] = w.value_a;
        row[col::BLINDING_A] = w.blinding_a;
        row[col::VALUE_B] = w.value_b;
        row[col::BLINDING_B] = w.blinding_b;

        let diff = w.compute_diff();
        row[col::DIFF] = diff;

        match w.relation {
            RelationType::Equal => {
                // For Equal: diff must be zero. No bits needed.
            }
            RelationType::NotEqual => {
                // For NotEqual: provide the multiplicative inverse of diff.
                if let Some(inv) = diff.inverse() {
                    row[col::NEQ_INVERSE] = inv;
                }
            }
            _ => {
                // For all range-based relations: bit decomposition of diff.
                let diff_val = diff.as_u32();
                for i in 0..RELATIONAL_DIFF_BITS {
                    let bit = (diff_val >> i) & 1;
                    row[col::diff_bit(i)] = BabyBear::new(bit);
                }
            }
        }

        // Result bit is always 1 for a valid proof.
        row[col::RESULT_BIT] = BabyBear::ONE;

        let commitment_a = w.commitment_a();
        let commitment_b = w.commitment_b();
        let public_inputs = vec![commitment_a, commitment_b, BabyBear::ONE];

        (vec![row], public_inputs)
    }
}

/// Compute a value commitment: `Poseidon2(value, blinding)`.
///
/// This creates a binding, hiding commitment to a value. The blinding factor
/// provides hiding (two different blindings produce unlinkable commitments for
/// the same value). The Poseidon2 binding property ensures a committed value
/// cannot be changed after publication.
pub fn compute_value_commitment(value: BabyBear, blinding: BabyBear) -> BabyBear {
    poseidon2::hash_2_to_1(value, blinding)
}

/// A complete relational predicate proof result.
#[derive(Clone, Debug)]
pub struct RelationalPredicateProof {
    /// The type of relation that was proven.
    pub relation: RelationType,
    /// Commitment to value A (public input).
    pub commitment_a: BabyBear,
    /// Commitment to value B (public input).
    pub commitment_b: BabyBear,
    /// The constraint proof (trace digest + public inputs).
    pub proof: crate::constraint_prover::ConstraintProof,
}

/// Generate a relational predicate proof from a witness.
///
/// The prover must know BOTH values (this is the comparison service).
/// Returns `None` if the relation is not satisfiable (the statement is false)
/// or if proof generation fails.
pub fn prove_relational(witness: RelationalPredicateWitness) -> Option<RelationalPredicateProof> {
    if !witness.is_satisfiable() {
        return None;
    }

    let relation = witness.relation;
    let commitment_a = witness.commitment_a();
    let commitment_b = witness.commitment_b();

    let air = RelationalPredicateAir::new(witness);
    let proof = crate::constraint_prover::ConstraintProof::generate(&air)?;

    Some(RelationalPredicateProof {
        relation,
        commitment_a,
        commitment_b,
        proof,
    })
}

/// Verify a relational predicate proof against expected commitments.
///
/// The verifier provides the commitments they expect (published by Alice and Bob)
/// and checks the proof is consistent. The verifier learns ONLY that the relation
/// holds -- neither value_a nor value_b is revealed.
pub fn verify_relational(
    proof: &RelationalPredicateProof,
    commitment_a: BabyBear,
    commitment_b: BabyBear,
) -> bool {
    if proof.commitment_a != commitment_a || proof.commitment_b != commitment_b {
        return false;
    }
    let expected_pi = [commitment_a, commitment_b, BabyBear::ONE];
    proof.proof.verify(&expected_pi)
}

/// High-level protocol helper: prove a value comparison between two parties.
///
/// This function is called by the comparison service that has received both
/// sealed values. It generates the proof that can be verified by anyone who
/// knows the commitments.
///
/// # Arguments
///
/// * `value_a` - Alice's private value
/// * `blinding_a` - Alice's blinding factor for her commitment
/// * `value_b` - Bob's private value
/// * `blinding_b` - Bob's blinding factor for his commitment
/// * `relation` - The relation to prove (e.g., GreaterThan)
///
/// # Returns
///
/// The proof if the relation holds, or `None` if the relation is false.
pub fn prove_value_comparison(
    value_a: BabyBear,
    blinding_a: BabyBear,
    value_b: BabyBear,
    blinding_b: BabyBear,
    relation: RelationType,
) -> Option<RelationalPredicateProof> {
    let witness = RelationalPredicateWitness {
        value_a,
        blinding_a,
        value_b,
        blinding_b,
        relation,
    };
    prove_relational(witness)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint_prover::ConstraintProver;

    // =========================================================================
    // GreaterThan tests
    // =========================================================================

    #[test]
    fn test_relational_greater_than_passes() {
        // Prove: a(100) > b(50)
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(100),
            blinding_a: BabyBear::new(111),
            value_b: BabyBear::new(50),
            blinding_b: BabyBear::new(222),
            relation: RelationType::GreaterThan,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GT 100 > 50 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_relational_greater_than_fails_when_equal() {
        // Prove: a(50) > b(50) -- should FAIL
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(50),
            blinding_a: BabyBear::new(111),
            value_b: BabyBear::new(50),
            blinding_b: BabyBear::new(222),
            relation: RelationType::GreaterThan,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "GT 50 > 50 should fail");
    }

    #[test]
    fn test_relational_greater_than_fails_when_less() {
        // Prove: a(50) > b(100) -- should FAIL
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(50),
            blinding_a: BabyBear::new(111),
            value_b: BabyBear::new(100),
            blinding_b: BabyBear::new(222),
            relation: RelationType::GreaterThan,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "GT 50 > 100 should fail");
    }

    // =========================================================================
    // LessThan tests
    // =========================================================================

    #[test]
    fn test_relational_less_than_passes() {
        // Prove: a(30) < b(100)
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(30),
            blinding_a: BabyBear::new(333),
            value_b: BabyBear::new(100),
            blinding_b: BabyBear::new(444),
            relation: RelationType::LessThan,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "LT 30 < 100 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_relational_less_than_fails_when_greater() {
        // Prove: a(100) < b(30) -- should FAIL
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(100),
            blinding_a: BabyBear::new(333),
            value_b: BabyBear::new(30),
            blinding_b: BabyBear::new(444),
            relation: RelationType::LessThan,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "LT 100 < 30 should fail");
    }

    // =========================================================================
    // GreaterOrEqual / LessOrEqual tests
    // =========================================================================

    #[test]
    fn test_relational_gte_equal_passes() {
        // Prove: a(50) >= b(50) (equal case)
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(50),
            blinding_a: BabyBear::new(555),
            value_b: BabyBear::new(50),
            blinding_b: BabyBear::new(666),
            relation: RelationType::GreaterOrEqual,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GTE 50 >= 50 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_relational_gte_greater_passes() {
        // Prove: a(100) >= b(50)
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(100),
            blinding_a: BabyBear::new(555),
            value_b: BabyBear::new(50),
            blinding_b: BabyBear::new(666),
            relation: RelationType::GreaterOrEqual,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "GTE 100 >= 50 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_relational_lte_passes() {
        // Prove: a(30) <= b(100)
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(30),
            blinding_a: BabyBear::new(777),
            value_b: BabyBear::new(100),
            blinding_b: BabyBear::new(888),
            relation: RelationType::LessOrEqual,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "LTE 30 <= 100 should pass: {:?}",
            result.violations()
        );
    }

    // =========================================================================
    // Equal / NotEqual tests
    // =========================================================================

    #[test]
    fn test_relational_equal_passes() {
        // Prove: a(42) == b(42)
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(42),
            blinding_a: BabyBear::new(100),
            value_b: BabyBear::new(42),
            blinding_b: BabyBear::new(200),
            relation: RelationType::Equal,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "EQ 42 == 42 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_relational_equal_fails_when_different() {
        // Prove: a(42) == b(43) -- should FAIL
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(42),
            blinding_a: BabyBear::new(100),
            value_b: BabyBear::new(43),
            blinding_b: BabyBear::new(200),
            relation: RelationType::Equal,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "EQ 42 == 43 should fail");
        let has_eq_violation = result
            .violations()
            .iter()
            .any(|v| v.constraint_name == "equal_diff_zero");
        assert!(
            has_eq_violation,
            "Should have equal_diff_zero violation, got: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_relational_not_equal_passes() {
        // Prove: a(42) != b(100)
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(42),
            blinding_a: BabyBear::new(300),
            value_b: BabyBear::new(100),
            blinding_b: BabyBear::new(400),
            relation: RelationType::NotEqual,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "NEQ 42 != 100 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_relational_not_equal_fails_when_same() {
        // Prove: a(42) != b(42) -- should FAIL
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(42),
            blinding_a: BabyBear::new(300),
            value_b: BabyBear::new(42),
            blinding_b: BabyBear::new(400),
            relation: RelationType::NotEqual,
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "NEQ 42 != 42 should fail");
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
    // DiffGreaterThan tests (relative standing)
    // =========================================================================

    #[test]
    fn test_relational_diff_greater_than_passes() {
        // Prove: a(200) - b(50) > threshold(100)
        // i.e., 150 > 100 -- TRUE
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(200),
            blinding_a: BabyBear::new(500),
            value_b: BabyBear::new(50),
            blinding_b: BabyBear::new(600),
            relation: RelationType::DiffGreaterThan(BabyBear::new(100)),
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "DiffGT (200-50=150) > 100 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_relational_diff_greater_than_fails() {
        // Prove: a(120) - b(50) > threshold(100)
        // i.e., 70 > 100 -- FALSE
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(120),
            blinding_a: BabyBear::new(500),
            value_b: BabyBear::new(50),
            blinding_b: BabyBear::new(600),
            relation: RelationType::DiffGreaterThan(BabyBear::new(100)),
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "DiffGT (120-50=70) > 100 should fail");
    }

    // =========================================================================
    // SumGreaterThan tests (joint qualification)
    // =========================================================================

    #[test]
    fn test_relational_sum_greater_than_passes() {
        // Prove: a(300) + b(400) > threshold(500)
        // i.e., 700 > 500 -- TRUE
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(300),
            blinding_a: BabyBear::new(700),
            value_b: BabyBear::new(400),
            blinding_b: BabyBear::new(800),
            relation: RelationType::SumGreaterThan(BabyBear::new(500)),
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(
            result.is_valid(),
            "SumGT (300+400=700) > 500 should pass: {:?}",
            result.violations()
        );
    }

    #[test]
    fn test_relational_sum_greater_than_fails() {
        // Prove: a(200) + b(200) > threshold(500)
        // i.e., 400 > 500 -- FALSE
        let witness = RelationalPredicateWitness {
            value_a: BabyBear::new(200),
            blinding_a: BabyBear::new(700),
            value_b: BabyBear::new(200),
            blinding_b: BabyBear::new(800),
            relation: RelationType::SumGreaterThan(BabyBear::new(500)),
        };

        let air = RelationalPredicateAir::new(witness);
        let result = ConstraintProver::verify(&air);
        assert!(!result.is_valid(), "SumGT (200+200=400) > 500 should fail");
    }

    // =========================================================================
    // prove_relational / verify_relational integration
    // =========================================================================

    #[test]
    fn test_prove_and_verify_greater_than() {
        let value_a = BabyBear::new(100);
        let blinding_a = BabyBear::new(111);
        let value_b = BabyBear::new(50);
        let blinding_b = BabyBear::new(222);

        let proof = prove_value_comparison(
            value_a,
            blinding_a,
            value_b,
            blinding_b,
            RelationType::GreaterThan,
        )
        .expect("should produce proof");

        let commitment_a = compute_value_commitment(value_a, blinding_a);
        let commitment_b = compute_value_commitment(value_b, blinding_b);

        assert!(verify_relational(&proof, commitment_a, commitment_b));
    }

    #[test]
    fn test_prove_returns_none_for_false_statement() {
        // a(50) > b(100) is false
        let result = prove_value_comparison(
            BabyBear::new(50),
            BabyBear::new(111),
            BabyBear::new(100),
            BabyBear::new(222),
            RelationType::GreaterThan,
        );
        assert!(result.is_none(), "Cannot prove false statement");
    }

    #[test]
    fn test_verify_fails_with_wrong_commitment_a() {
        let value_a = BabyBear::new(100);
        let blinding_a = BabyBear::new(111);
        let value_b = BabyBear::new(50);
        let blinding_b = BabyBear::new(222);

        let proof = prove_value_comparison(
            value_a,
            blinding_a,
            value_b,
            blinding_b,
            RelationType::GreaterThan,
        )
        .expect("should produce proof");

        let commitment_b = compute_value_commitment(value_b, blinding_b);
        // Use wrong commitment for A
        let wrong_commitment_a = BabyBear::new(99999);
        assert!(!verify_relational(&proof, wrong_commitment_a, commitment_b));
    }

    #[test]
    fn test_verify_fails_with_wrong_commitment_b() {
        let value_a = BabyBear::new(100);
        let blinding_a = BabyBear::new(111);
        let value_b = BabyBear::new(50);
        let blinding_b = BabyBear::new(222);

        let proof = prove_value_comparison(
            value_a,
            blinding_a,
            value_b,
            blinding_b,
            RelationType::GreaterThan,
        )
        .expect("should produce proof");

        let commitment_a = compute_value_commitment(value_a, blinding_a);
        // Use wrong commitment for B
        let wrong_commitment_b = BabyBear::new(99999);
        assert!(!verify_relational(&proof, commitment_a, wrong_commitment_b));
    }

    // =========================================================================
    // Unlinkability: different blindings produce different commitments
    // =========================================================================

    #[test]
    fn test_different_blindings_produce_different_commitments() {
        let value = BabyBear::new(1000);
        let blinding_1 = BabyBear::new(42);
        let blinding_2 = BabyBear::new(43);

        let c1 = compute_value_commitment(value, blinding_1);
        let c2 = compute_value_commitment(value, blinding_2);

        assert_ne!(
            c1, c2,
            "Same value with different blindings must produce different commitments"
        );
    }

    #[test]
    fn test_same_blinding_same_value_produces_same_commitment() {
        let value = BabyBear::new(1000);
        let blinding = BabyBear::new(42);

        let c1 = compute_value_commitment(value, blinding);
        let c2 = compute_value_commitment(value, blinding);

        assert_eq!(c1, c2, "Deterministic commitment");
    }

    // =========================================================================
    // Auction scenario: prove my bid > their bid
    // =========================================================================

    #[test]
    fn test_auction_scenario() {
        // Alice bids 5000, Bob bids 3000. Alice wants to prove she won.
        let alice_bid = BabyBear::new(5000);
        let alice_blinding = BabyBear::new(98765);
        let bob_bid = BabyBear::new(3000);
        let bob_blinding = BabyBear::new(12345);

        // Both publish commitments
        let alice_commitment = compute_value_commitment(alice_bid, alice_blinding);
        let bob_commitment = compute_value_commitment(bob_bid, bob_blinding);

        // Comparison service proves Alice > Bob
        let proof = prove_value_comparison(
            alice_bid,
            alice_blinding,
            bob_bid,
            bob_blinding,
            RelationType::GreaterThan,
        )
        .expect("Alice's bid is higher");

        // Anyone can verify: the bid behind alice_commitment > the bid behind bob_commitment
        assert!(verify_relational(&proof, alice_commitment, bob_commitment));

        // Neither Alice nor Bob's actual bid is revealed to verifiers.
        // The proof only shows: C_a's value > C_b's value.
    }

    // =========================================================================
    // Joint qualification scenario: prove combined balance > threshold
    // =========================================================================

    #[test]
    fn test_joint_qualification_scenario() {
        // Alice has balance 300, Bob has balance 400.
        // They need to prove combined balance > 500 for a joint loan.
        let alice_balance = BabyBear::new(300);
        let alice_blinding = BabyBear::new(11111);
        let bob_balance = BabyBear::new(400);
        let bob_blinding = BabyBear::new(22222);

        let alice_commitment = compute_value_commitment(alice_balance, alice_blinding);
        let bob_commitment = compute_value_commitment(bob_balance, bob_blinding);

        // Prove combined > 500
        let proof = prove_value_comparison(
            alice_balance,
            alice_blinding,
            bob_balance,
            bob_blinding,
            RelationType::SumGreaterThan(BabyBear::new(500)),
        )
        .expect("combined balance qualifies");

        assert!(verify_relational(&proof, alice_commitment, bob_commitment));
    }

    // =========================================================================
    // Reputation scenario: prove reputation difference > threshold
    // =========================================================================

    #[test]
    fn test_reputation_scenario() {
        // Alice has reputation 800, Bob has reputation 200.
        // Prove Alice's reputation exceeds Bob's by more than 500.
        let alice_rep = BabyBear::new(800);
        let alice_blinding = BabyBear::new(33333);
        let bob_rep = BabyBear::new(200);
        let bob_blinding = BabyBear::new(44444);

        let alice_commitment = compute_value_commitment(alice_rep, alice_blinding);
        let bob_commitment = compute_value_commitment(bob_rep, bob_blinding);

        // Prove: alice_rep - bob_rep > 500 (i.e., 600 > 500)
        let proof = prove_value_comparison(
            alice_rep,
            alice_blinding,
            bob_rep,
            bob_blinding,
            RelationType::DiffGreaterThan(BabyBear::new(500)),
        )
        .expect("reputation difference qualifies");

        assert!(verify_relational(&proof, alice_commitment, bob_commitment));
    }
}
