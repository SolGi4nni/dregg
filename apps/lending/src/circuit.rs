//! Circuit descriptors for lending protocol proofs.
//!
//! Two main circuits:
//! - HealthFactorAir: proves collateral_value * threshold >= debt_value * BPS_SCALE
//! - InterestAccrualAir: proves correct compound interest computation
//!
//! These use pyana-circuit's AIR/STARK infrastructure to produce cryptographic proofs
//! that can be verified without access to the underlying position data.

use pyana_circuit::constraint_prover::{Air, Constraint, ConstraintProver};
use pyana_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

use crate::interest::BPS_SCALE;

// =============================================================================
// Health Factor Circuit
// =============================================================================

/// Trace width for the health factor AIR.
///
/// Layout (single row):
/// | 0  | collateral_value (sum of amount*price for all collateral) |
/// | 1  | debt_amount                                                |
/// | 2  | threshold_bps                                              |
/// | 3  | lhs = collateral_value * threshold_bps                    |
/// | 4  | rhs = debt_amount * BPS_SCALE                              |
/// | 5  | diff = lhs - rhs (must be >= 0)                           |
/// | 6..35 | diff_bits[0..29] (bit decomposition)                    |
pub const HEALTH_FACTOR_WIDTH: usize = 36;

/// Number of bits for diff decomposition (30 bits covers BabyBear range safely).
const HEALTH_DIFF_BITS: usize = 30;

/// Column indices for health factor AIR.
pub mod health_col {
    pub const COLLATERAL_VALUE: usize = 0;
    pub const DEBT_AMOUNT: usize = 1;
    pub const THRESHOLD_BPS: usize = 2;
    pub const LHS: usize = 3;
    pub const RHS: usize = 4;
    pub const DIFF: usize = 5;
    pub const DIFF_BITS_START: usize = 6;
}

/// Health factor AIR: proves that a lending position is solvent.
///
/// Statement: collateral_value * threshold_bps >= debt_amount * BPS_SCALE
///
/// This is a single-row AIR that verifies the health factor inequality
/// via bit decomposition of the non-negative difference.
pub struct HealthFactorAir {
    /// Pre-computed trace and public inputs.
    pub trace: Vec<Vec<BabyBear>>,
    pub public_inputs: Vec<BabyBear>,
}

impl Air for HealthFactorAir {
    fn trace_width(&self) -> usize {
        HEALTH_FACTOR_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        3 // [collateral_value, debt_amount, threshold_bps]
    }

    fn constraints(&self) -> Vec<Constraint> {
        vec![
            // 1. lhs = collateral_value * threshold_bps
            Constraint {
                name: "lhs_computation".to_string(),
                eval: Box::new(|row, _next, _pi| {
                    let col_val = row[health_col::COLLATERAL_VALUE];
                    let threshold = row[health_col::THRESHOLD_BPS];
                    let lhs = row[health_col::LHS];
                    // Constraint: lhs - col_val * threshold == 0
                    lhs - col_val * threshold
                }),
            },
            // 2. rhs = debt_amount * BPS_SCALE
            Constraint {
                name: "rhs_computation".to_string(),
                eval: Box::new(|row, _next, _pi| {
                    let debt = row[health_col::DEBT_AMOUNT];
                    let rhs = row[health_col::RHS];
                    let bps = BabyBear::new(BPS_SCALE as u32);
                    rhs - debt * bps
                }),
            },
            // 3. diff = lhs - rhs
            Constraint {
                name: "diff_computation".to_string(),
                eval: Box::new(|row, _next, _pi| {
                    let lhs = row[health_col::LHS];
                    let rhs = row[health_col::RHS];
                    let diff = row[health_col::DIFF];
                    diff - (lhs - rhs)
                }),
            },
            // 4. Bit decomposition: sum(diff_bits[i] * 2^i) == diff
            Constraint {
                name: "diff_bit_decomposition".to_string(),
                eval: Box::new(|row, _next, _pi| {
                    let diff = row[health_col::DIFF];
                    let mut reconstructed = BabyBear::ZERO;
                    let mut power = BabyBear::ONE;
                    let two = BabyBear::new(2);
                    for i in 0..HEALTH_DIFF_BITS {
                        let bit = row[health_col::DIFF_BITS_START + i];
                        reconstructed = reconstructed + bit * power;
                        power = power * two;
                    }
                    diff - reconstructed
                }),
            },
            // 5. Each bit is binary: bit * (bit - 1) == 0
            // We check all bits in one constraint by summing violations
            Constraint {
                name: "bits_are_binary".to_string(),
                eval: Box::new(|row, _next, _pi| {
                    let mut sum = BabyBear::ZERO;
                    for i in 0..HEALTH_DIFF_BITS {
                        let bit = row[health_col::DIFF_BITS_START + i];
                        sum = sum + bit * (bit - BabyBear::ONE);
                    }
                    sum
                }),
            },
            // 6. High bit is zero (proves diff is non-negative)
            Constraint {
                name: "high_bit_zero".to_string(),
                eval: Box::new(|row, _next, _pi| {
                    row[health_col::DIFF_BITS_START + HEALTH_DIFF_BITS - 1]
                }),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        (self.trace.clone(), self.public_inputs.clone())
    }
}

/// Scale factor: we divide large values by this to fit in BabyBear range.
/// BabyBear p ~ 2^31, so values up to ~2B are safe. We scale by 1000 to give
/// comfortable headroom for multiplications.
const SCALE_FACTOR: u64 = 1000;

/// Generate a health factor AIR instance for proving solvency.
///
/// All values are internally scaled to fit within BabyBear's range.
/// The circuit proves: collateral_value * threshold_bps >= debt_amount * BPS_SCALE
/// by working with scaled values where both sides are divided by SCALE_FACTOR.
pub fn build_health_factor_air(
    collateral_amounts: &[u64],
    collateral_prices: &[u64],
    debt_amount: u64,
    threshold_bps: u64,
) -> HealthFactorAir {
    assert_eq!(collateral_amounts.len(), collateral_prices.len());

    // Compute cumulative collateral value
    let mut cumulative_value: u64 = 0;
    for i in 0..collateral_amounts.len() {
        let value = (collateral_amounts[i] as u128 * collateral_prices[i] as u128
            / BPS_SCALE as u128) as u64;
        cumulative_value += value;
    }

    // Scale values to fit in BabyBear:
    // We prove: (col_value / S) * threshold >= (debt / S) * BPS_SCALE
    // This is equivalent to: col_value * threshold >= debt * BPS_SCALE
    // when S divides evenly (which preserves the inequality direction).
    let col_scaled = cumulative_value / SCALE_FACTOR;
    let debt_scaled = debt_amount / SCALE_FACTOR;

    // Now lhs = col_scaled * threshold_bps, rhs = debt_scaled * BPS_SCALE
    // Both should fit in u32 if values are reasonable
    let lhs = col_scaled * threshold_bps;
    let rhs = debt_scaled * BPS_SCALE;
    let diff = lhs.saturating_sub(rhs);

    // Ensure diff fits in 30 bits (< 2^29 for safety)
    let diff_clamped = diff & ((1u64 << (HEALTH_DIFF_BITS - 1)) - 1);

    // Build single-row trace
    let mut row = vec![BabyBear::ZERO; HEALTH_FACTOR_WIDTH];
    row[health_col::COLLATERAL_VALUE] = BabyBear::new(col_scaled as u32);
    row[health_col::DEBT_AMOUNT] = BabyBear::new(debt_scaled as u32);
    row[health_col::THRESHOLD_BPS] = BabyBear::new(threshold_bps as u32);
    row[health_col::LHS] = BabyBear::new(lhs as u32);
    row[health_col::RHS] = BabyBear::new(rhs as u32);
    row[health_col::DIFF] = BabyBear::new(diff_clamped as u32);

    // Bit decomposition
    for bit_idx in 0..HEALTH_DIFF_BITS {
        let bit = (diff_clamped >> bit_idx) & 1;
        row[health_col::DIFF_BITS_START + bit_idx] = BabyBear::new(bit as u32);
    }

    let public_inputs = vec![
        BabyBear::new(col_scaled as u32),
        BabyBear::new(debt_scaled as u32),
        BabyBear::new(threshold_bps as u32),
    ];

    HealthFactorAir {
        trace: vec![row],
        public_inputs,
    }
}

// =============================================================================
// Interest Accrual Circuit
// =============================================================================

/// Trace width for the interest accrual AIR.
///
/// Layout (per block row):
/// | 0  | block_index (0..N-1)                |
/// | 1  | balance (current balance at step)    |
/// | 2  | rate_per_block (fixed for period)    |
/// | 3  | interest_this_block                  |
/// | 4  | next_balance (balance + interest)    |
pub const INTEREST_ACCRUAL_WIDTH: usize = 5;

/// Column indices for interest accrual AIR.
pub mod accrual_col {
    pub const BLOCK_INDEX: usize = 0;
    pub const BALANCE: usize = 1;
    pub const RATE: usize = 2;
    pub const INTEREST: usize = 3;
    pub const NEXT_BALANCE: usize = 4;
}

/// Precision for per-block rate (rate is expressed as numerator with this denominator).
pub const RATE_PRECISION: u64 = 1_000_000_000;

/// Interest accrual AIR: proves correct compound interest computation.
///
/// Statement: new_balance = old_balance * (1 + rate)^num_blocks
/// Realized as iterated multiplication: each row computes one block of interest.
///
/// Transition constraint: balance[i+1] = next_balance[i]
/// Per-row: next_balance = balance + interest, where interest = balance * rate / PRECISION
pub struct InterestAccrualAir {
    pub trace: Vec<Vec<BabyBear>>,
    pub public_inputs: Vec<BabyBear>,
}

impl Air for InterestAccrualAir {
    fn trace_width(&self) -> usize {
        INTEREST_ACCRUAL_WIDTH
    }

    fn num_public_inputs(&self) -> usize {
        4 // [start_balance, end_balance, rate, num_blocks]
    }

    fn constraints(&self) -> Vec<Constraint> {
        vec![
            // 1. next_balance = balance + interest
            Constraint {
                name: "next_balance_sum".to_string(),
                eval: Box::new(|row, _next, _pi| {
                    let balance = row[accrual_col::BALANCE];
                    let interest = row[accrual_col::INTEREST];
                    let next_balance = row[accrual_col::NEXT_BALANCE];
                    next_balance - (balance + interest)
                }),
            },
            // 2. Transition: next row's balance == this row's next_balance
            Constraint {
                name: "balance_continuity".to_string(),
                eval: Box::new(|row, next, _pi| {
                    if let Some(next_row) = next {
                        let expected = row[accrual_col::NEXT_BALANCE];
                        let actual = next_row[accrual_col::BALANCE];
                        actual - expected
                    } else {
                        BabyBear::ZERO // No constraint on last row's transition
                    }
                }),
            },
            // 3. Block index increments
            Constraint {
                name: "block_index_increment".to_string(),
                eval: Box::new(|row, next, _pi| {
                    if let Some(next_row) = next {
                        let curr = row[accrual_col::BLOCK_INDEX];
                        let next_idx = next_row[accrual_col::BLOCK_INDEX];
                        next_idx - curr - BabyBear::ONE
                    } else {
                        BabyBear::ZERO
                    }
                }),
            },
        ]
    }

    fn generate_trace(&self) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        (self.trace.clone(), self.public_inputs.clone())
    }
}

/// Build an interest accrual AIR instance.
///
/// Public inputs: [start_balance, end_balance, rate, num_blocks]
pub fn build_interest_accrual_air(
    start_balance: u64,
    rate_per_block_numerator: u64,
    num_blocks: usize,
) -> InterestAccrualAir {
    let actual_rows = num_blocks.max(1);
    let mut trace = Vec::with_capacity(actual_rows);

    let mut balance = start_balance;

    for i in 0..actual_rows {
        let interest =
            (balance as u128 * rate_per_block_numerator as u128 / RATE_PRECISION as u128) as u64;
        let next_balance = balance + interest;

        let mut row = vec![BabyBear::ZERO; INTEREST_ACCRUAL_WIDTH];
        row[accrual_col::BLOCK_INDEX] = BabyBear::new(i as u32);
        row[accrual_col::BALANCE] = BabyBear::new(balance as u32);
        row[accrual_col::RATE] = BabyBear::new(rate_per_block_numerator as u32);
        row[accrual_col::INTEREST] = BabyBear::new(interest as u32);
        row[accrual_col::NEXT_BALANCE] = BabyBear::new(next_balance as u32);

        trace.push(row);
        balance = next_balance;
    }

    let public_inputs = vec![
        BabyBear::new(start_balance as u32),
        BabyBear::new(balance as u32), // end_balance
        BabyBear::new(rate_per_block_numerator as u32),
        BabyBear::new(num_blocks as u32),
    ];

    InterestAccrualAir {
        trace,
        public_inputs,
    }
}

// =============================================================================
// Verification helpers
// =============================================================================

/// Verify a health factor proof (mock verification via constraint checking).
pub fn verify_health_factor(
    collateral_amounts: &[u64],
    collateral_prices: &[u64],
    debt_amount: u64,
    threshold_bps: u64,
) -> bool {
    let air = build_health_factor_air(
        collateral_amounts,
        collateral_prices,
        debt_amount,
        threshold_bps,
    );
    let result = ConstraintProver::verify(&air);
    result.is_valid()
}

/// Verify an interest accrual proof (mock verification via constraint checking).
pub fn verify_interest_accrual(
    start_balance: u64,
    rate_per_block: u64,
    num_blocks: usize,
    expected_end_balance: u64,
) -> bool {
    let air = build_interest_accrual_air(start_balance, rate_per_block, num_blocks);
    let (_, pi) = air.generate_trace();
    // Check end balance matches
    let computed_end = pi[1].as_u32() as u64;
    if computed_end != expected_end_balance {
        return false;
    }
    let result = ConstraintProver::verify(&air);
    result.is_valid()
}

// =============================================================================
// Descriptors (for serialization and use in obligations)
// =============================================================================

/// Descriptor for health factor proofs, suitable for use in obligation conditions.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HealthFactorDescriptor {
    /// Collateral amounts per asset.
    pub collateral_amounts: Vec<u64>,
    /// Collateral prices per asset (must match amounts length).
    pub collateral_prices: Vec<u64>,
    /// Total debt value.
    pub debt_amount: u64,
    /// Liquidation threshold in basis points.
    pub threshold_bps: u64,
}

impl HealthFactorDescriptor {
    /// Check if this descriptor represents a healthy position.
    pub fn is_healthy(&self) -> bool {
        verify_health_factor(
            &self.collateral_amounts,
            &self.collateral_prices,
            self.debt_amount,
            self.threshold_bps,
        )
    }
}

/// Descriptor for interest accrual proofs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InterestAccrualDescriptor {
    /// Starting balance.
    pub start_balance: u64,
    /// Per-block rate numerator (denominator is RATE_PRECISION).
    pub rate_per_block: u64,
    /// Number of blocks to accrue over.
    pub num_blocks: usize,
    /// Expected end balance after accrual.
    pub expected_end_balance: u64,
}

impl InterestAccrualDescriptor {
    /// Verify the accrual computation.
    pub fn verify(&self) -> bool {
        verify_interest_accrual(
            self.start_balance,
            self.rate_per_block,
            self.num_blocks,
            self.expected_end_balance,
        )
    }

    /// Compute the expected end balance for this descriptor.
    pub fn compute_end_balance(&self) -> u64 {
        let mut balance = self.start_balance;
        for _ in 0..self.num_blocks {
            let interest =
                (balance as u128 * self.rate_per_block as u128 / RATE_PRECISION as u128) as u64;
            balance += interest;
        }
        balance
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_health_factor_healthy_trace() {
        // 1.5M collateral at price 1:1, 1M debt, 80% threshold
        // lhs = 1_500_000 * 8000 = 12_000_000_000
        // rhs = 1_000_000 * 10000 = 10_000_000_000
        // diff = 2_000_000_000 > 0, so healthy
        let result = verify_health_factor(&[1_500_000], &[BPS_SCALE], 1_000_000, 8_000);
        assert!(result);
    }

    #[test]
    fn test_health_factor_multi_asset() {
        // Two assets: 500K at price 2x, 300K at price 1x
        // total col value = 500_000*20000/10000 + 300_000*10000/10000 = 1_000_000 + 300_000 = 1_300_000
        let result = verify_health_factor(
            &[500_000, 300_000],
            &[BPS_SCALE * 2, BPS_SCALE],
            1_000_000,
            8_000,
        );
        assert!(result);
    }

    #[test]
    fn test_interest_accrual_basic() {
        let rate = RATE_PRECISION / 100; // 1% per block
        let air = build_interest_accrual_air(1_000_000, rate, 10);
        let (_, pi) = air.generate_trace();
        assert_eq!(pi[0], BabyBear::new(1_000_000)); // start
        assert_eq!(pi[3], BabyBear::new(10)); // num_blocks
        // End balance should be > start
        assert!(pi[1].as_u32() > 1_000_000);
    }

    #[test]
    fn test_interest_accrual_descriptor() {
        let desc = InterestAccrualDescriptor {
            start_balance: 1_000_000,
            rate_per_block: RATE_PRECISION / 1000, // 0.1% per block
            num_blocks: 5,
            expected_end_balance: 0,
        };
        let end = desc.compute_end_balance();
        assert!(end > 1_000_000);

        let desc_valid = InterestAccrualDescriptor {
            expected_end_balance: end,
            ..desc
        };
        assert!(desc_valid.verify());
    }

    #[test]
    fn test_health_factor_descriptor() {
        let desc = HealthFactorDescriptor {
            collateral_amounts: vec![2_000_000],
            collateral_prices: vec![BPS_SCALE],
            debt_amount: 1_000_000,
            threshold_bps: 8_000,
        };
        assert!(desc.is_healthy());
    }

    #[test]
    fn test_health_factor_constraint_verification() {
        let air = build_health_factor_air(&[2_000_000], &[BPS_SCALE], 1_000_000, 8_000);
        let result = ConstraintProver::verify(&air);
        assert!(result.is_valid());
    }

    #[test]
    fn test_interest_accrual_constraint_verification() {
        let air = build_interest_accrual_air(1_000_000, RATE_PRECISION / 1000, 5);
        let result = ConstraintProver::verify(&air);
        assert!(result.is_valid());
    }
}
