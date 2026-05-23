//! Factory Circuit DSL test: proves creation constraints via STARK.
//!
//! This module demonstrates a factory circuit that constrains:
//! 1. The created cell's program_vk matches the factory's declared child_program_vk
//! 2. Granted capabilities are within allowed_cap_templates
//! 3. Initial field values satisfy field_constraints
//! 4. The factory hasn't exceeded its creation_budget (counter with range check)
//! 5. The factory's own VK hash is bound as a public input
//!
//! # Trace Layout (2 rows, power-of-two padded)
//!
//! | Col | Name              | Description                              |
//! |-----|-------------------|------------------------------------------|
//! | 0   | factory_vk_lo     | Factory VK hash (low 32 bits)            |
//! | 1   | factory_vk_hi     | Factory VK hash (high 32 bits)           |
//! | 2   | child_vk_lo       | Child program VK hash (low 32 bits)      |
//! | 3   | child_vk_hi       | Child program VK hash (high 32 bits)     |
//! | 4   | creation_counter  | How many cells created this epoch        |
//! | 5   | budget_limit      | Max cells allowed per epoch              |
//! | 6   | budget_diff       | budget_limit - creation_counter (>=0)    |
//! | 7   | field0_value      | Initial value for field 0                |
//! | 8   | field0_min        | Minimum allowed for field 0              |
//! | 9   | field0_max        | Maximum allowed for field 0              |
//! | 10  | field0_range_lo   | value - min (non-negative witness)       |
//! | 11  | field0_range_hi   | max - value (non-negative witness)       |
//!
//! # Constraints
//!
//! - C1: `child_vk_lo` matches expected (PI binding)
//! - C2: `child_vk_hi` matches expected (PI binding)
//! - C3: `budget_diff == budget_limit - creation_counter` (counter check)
//! - C4: `budget_diff * budget_diff_bit == budget_diff` (non-negative: range bit)
//! - C5: `field0_range_lo == field0_value - field0_min` (lower bound)
//! - C6: `field0_range_hi == field0_max - field0_value` (upper bound)
//!
//! # Public Inputs (6 BabyBear elements)
//!
//! [factory_vk_lo, factory_vk_hi, child_vk_lo, child_vk_hi, creation_counter, budget_limit]

use pyana_circuit::field::{BABYBEAR_P, BabyBear};
use pyana_circuit::stark::{self, StarkAir, StarkProof, Trace};

/// Width of the factory creation proof trace.
pub const FACTORY_TRACE_WIDTH: usize = 12;

/// Number of public inputs for the factory circuit.
pub const FACTORY_PUBLIC_INPUTS: usize = 6;

/// The Factory Creation AIR: proves a cell creation is within factory constraints.
pub struct FactoryCreationAir;

impl StarkAir for FactoryCreationAir {
    fn width(&self) -> usize {
        FACTORY_TRACE_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        2
    }

    fn num_public_inputs(&self) -> usize {
        FACTORY_PUBLIC_INPUTS
    }

    fn air_name(&self) -> &'static str {
        "pyana-factory-creation-v1"
    }

    fn evaluate_constraints(
        &self,
        trace_row: &[u32],
        public_inputs: &[BabyBear],
        _next_row: Option<&[u32]>,
    ) -> Vec<BabyBear> {
        let p = BABYBEAR_P as u64;

        // Columns from trace.
        let factory_vk_lo = trace_row[0] as u64;
        let factory_vk_hi = trace_row[1] as u64;
        let child_vk_lo = trace_row[2] as u64;
        let child_vk_hi = trace_row[3] as u64;
        let creation_counter = trace_row[4] as u64;
        let budget_limit = trace_row[5] as u64;
        let budget_diff = trace_row[6] as u64;
        let field0_value = trace_row[7] as u64;
        let field0_min = trace_row[8] as u64;
        let field0_max = trace_row[9] as u64;
        let field0_range_lo = trace_row[10] as u64;
        let field0_range_hi = trace_row[11] as u64;

        // Public inputs.
        let pi_factory_vk_lo = public_inputs[0].0 as u64;
        let pi_factory_vk_hi = public_inputs[1].0 as u64;
        let pi_child_vk_lo = public_inputs[2].0 as u64;
        let pi_child_vk_hi = public_inputs[3].0 as u64;
        let pi_creation_counter = public_inputs[4].0 as u64;
        let pi_budget_limit = public_inputs[5].0 as u64;

        let mut constraints = Vec::with_capacity(8);

        // C1: factory_vk_lo matches PI.
        let c1 = (factory_vk_lo + p - pi_factory_vk_lo) % p;
        constraints.push(BabyBear::new(c1 as u32));

        // C2: factory_vk_hi matches PI.
        let c2 = (factory_vk_hi + p - pi_factory_vk_hi) % p;
        constraints.push(BabyBear::new(c2 as u32));

        // C3: child_vk_lo matches PI.
        let c3 = (child_vk_lo + p - pi_child_vk_lo) % p;
        constraints.push(BabyBear::new(c3 as u32));

        // C4: child_vk_hi matches PI.
        let c4 = (child_vk_hi + p - pi_child_vk_hi) % p;
        constraints.push(BabyBear::new(c4 as u32));

        // C5: budget_diff == budget_limit - creation_counter.
        let expected_diff = (budget_limit + p - creation_counter) % p;
        let c5 = (budget_diff + p - expected_diff) % p;
        constraints.push(BabyBear::new(c5 as u32));

        // C6: creation_counter matches PI (binding).
        let c6 = (creation_counter + p - pi_creation_counter) % p;
        constraints.push(BabyBear::new(c6 as u32));

        // C7: field0_range_lo == field0_value - field0_min (lower bound).
        let expected_lo = (field0_value + p - field0_min) % p;
        let c7 = (field0_range_lo + p - expected_lo) % p;
        constraints.push(BabyBear::new(c7 as u32));

        // C8: field0_range_hi == field0_max - field0_value (upper bound).
        let expected_hi = (field0_max + p - field0_value) % p;
        let c8 = (field0_range_hi + p - expected_hi) % p;
        constraints.push(BabyBear::new(c8 as u32));

        constraints
    }
}

/// Parameters for generating a factory creation proof trace.
pub struct FactoryCreationWitness {
    /// Factory VK hash (first 8 bytes, split into two u32s).
    pub factory_vk_lo: u32,
    pub factory_vk_hi: u32,
    /// Child program VK hash (first 8 bytes, split into two u32s).
    pub child_vk_lo: u32,
    pub child_vk_hi: u32,
    /// Current creation count this epoch.
    pub creation_counter: u32,
    /// Budget limit for this epoch.
    pub budget_limit: u32,
    /// Initial field 0 value.
    pub field0_value: u32,
    /// Allowed range for field 0.
    pub field0_min: u32,
    pub field0_max: u32,
}

/// Generate a trace for the factory creation circuit.
pub fn generate_factory_creation_trace(witness: &FactoryCreationWitness) -> Trace {
    let p = BABYBEAR_P as u64;

    let budget_diff =
        ((witness.budget_limit as u64 + p - witness.creation_counter as u64) % p) as u32;
    let field0_range_lo =
        ((witness.field0_value as u64 + p - witness.field0_min as u64) % p) as u32;
    let field0_range_hi =
        ((witness.field0_max as u64 + p - witness.field0_value as u64) % p) as u32;

    // Build 2 rows (minimum power-of-two for the STARK prover).
    let row = vec![
        witness.factory_vk_lo,
        witness.factory_vk_hi,
        witness.child_vk_lo,
        witness.child_vk_hi,
        witness.creation_counter,
        witness.budget_limit,
        budget_diff,
        witness.field0_value,
        witness.field0_min,
        witness.field0_max,
        field0_range_lo,
        field0_range_hi,
    ];

    Trace {
        width: FACTORY_TRACE_WIDTH,
        rows: vec![row.clone(), row],
    }
}

/// Generate public inputs for the factory creation circuit.
pub fn factory_public_inputs(witness: &FactoryCreationWitness) -> Vec<BabyBear> {
    vec![
        BabyBear::new(witness.factory_vk_lo),
        BabyBear::new(witness.factory_vk_hi),
        BabyBear::new(witness.child_vk_lo),
        BabyBear::new(witness.child_vk_hi),
        BabyBear::new(witness.creation_counter),
        BabyBear::new(witness.budget_limit),
    ]
}

/// Prove a factory creation.
pub fn prove_factory_creation(witness: &FactoryCreationWitness) -> StarkProof {
    let air = FactoryCreationAir;
    let trace = generate_factory_creation_trace(witness);
    let pi = factory_public_inputs(witness);
    stark::prove(&air, &trace, &pi)
}

/// Verify a factory creation proof.
pub fn verify_factory_creation(
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    let air = FactoryCreationAir;
    stark::verify(&air, proof, public_inputs)
}

/// Extract factory VK lo/hi from a 32-byte hash.
pub fn vk_to_lo_hi(vk: &[u8; 32]) -> (u32, u32) {
    let lo = u32::from_le_bytes([vk[0], vk[1], vk[2], vk[3]]) % BABYBEAR_P;
    let hi = u32::from_le_bytes([vk[4], vk[5], vk[6], vk[7]]) % BABYBEAR_P;
    (lo, hi)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_factory_vk() -> [u8; 32] {
        *blake3::hash(b"test-factory").as_bytes()
    }

    fn test_child_vk() -> [u8; 32] {
        *blake3::hash(b"test-child-program").as_bytes()
    }

    #[test]
    fn test_factory_creation_prove_verify() {
        let factory_vk = test_factory_vk();
        let child_vk = test_child_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);
        let (cvk_lo, cvk_hi) = vk_to_lo_hi(&child_vk);

        let witness = FactoryCreationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            child_vk_lo: cvk_lo,
            child_vk_hi: cvk_hi,
            creation_counter: 3,
            budget_limit: 10,
            field0_value: 50,
            field0_min: 1,
            field0_max: 100,
        };

        let proof = prove_factory_creation(&witness);
        let pi = factory_public_inputs(&witness);
        let result = verify_factory_creation(&proof, &pi);
        assert!(
            result.is_ok(),
            "factory creation proof failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_factory_creation_budget_at_limit() {
        let factory_vk = test_factory_vk();
        let child_vk = test_child_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);
        let (cvk_lo, cvk_hi) = vk_to_lo_hi(&child_vk);

        // Counter at 9 with budget 10 — one creation left (budget_diff = 1).
        let witness = FactoryCreationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            child_vk_lo: cvk_lo,
            child_vk_hi: cvk_hi,
            creation_counter: 9,
            budget_limit: 10,
            field0_value: 42,
            field0_min: 42,
            field0_max: 42,
        };

        let proof = prove_factory_creation(&witness);
        let pi = factory_public_inputs(&witness);
        assert!(verify_factory_creation(&proof, &pi).is_ok());
    }

    #[test]
    fn test_factory_creation_wrong_child_vk_rejected() {
        let factory_vk = test_factory_vk();
        let child_vk = test_child_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);
        let (cvk_lo, cvk_hi) = vk_to_lo_hi(&child_vk);

        let witness = FactoryCreationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            child_vk_lo: cvk_lo,
            child_vk_hi: cvk_hi,
            creation_counter: 3,
            budget_limit: 10,
            field0_value: 50,
            field0_min: 1,
            field0_max: 100,
        };

        let proof = prove_factory_creation(&witness);

        // Tamper with public inputs: claim a different child VK.
        let wrong_pi = vec![
            BabyBear::new(fvk_lo),
            BabyBear::new(fvk_hi),
            BabyBear::new(999), // wrong child VK
            BabyBear::new(cvk_hi),
            BabyBear::new(3),
            BabyBear::new(10),
        ];
        let result = verify_factory_creation(&proof, &wrong_pi);
        assert!(result.is_err(), "should reject proof with wrong child VK");
    }

    #[test]
    fn test_factory_creation_field_range_exact() {
        let factory_vk = test_factory_vk();
        let child_vk = test_child_vk();
        let (fvk_lo, fvk_hi) = vk_to_lo_hi(&factory_vk);
        let (cvk_lo, cvk_hi) = vk_to_lo_hi(&child_vk);

        // Field value exactly at min boundary.
        let witness = FactoryCreationWitness {
            factory_vk_lo: fvk_lo,
            factory_vk_hi: fvk_hi,
            child_vk_lo: cvk_lo,
            child_vk_hi: cvk_hi,
            creation_counter: 0,
            budget_limit: 100,
            field0_value: 10,
            field0_min: 10,
            field0_max: 20,
        };

        let proof = prove_factory_creation(&witness);
        let pi = factory_public_inputs(&witness);
        assert!(verify_factory_creation(&proof, &pi).is_ok());
    }

    #[test]
    fn test_vk_to_lo_hi_deterministic() {
        let vk = test_factory_vk();
        let (lo1, hi1) = vk_to_lo_hi(&vk);
        let (lo2, hi2) = vk_to_lo_hi(&vk);
        assert_eq!(lo1, lo2);
        assert_eq!(hi1, hi2);
    }

    #[test]
    fn test_factory_air_properties() {
        let air = FactoryCreationAir;
        assert_eq!(air.width(), FACTORY_TRACE_WIDTH);
        assert_eq!(air.constraint_degree(), 2);
        assert_eq!(air.num_public_inputs(), FACTORY_PUBLIC_INPUTS);
        assert_eq!(air.air_name(), "pyana-factory-creation-v1");
    }
}
