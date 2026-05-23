//! Interest rate model: utilization-based rates for lending pools.
//!
//! Implements a kinked rate model similar to Aave/Compound:
//! - Below optimal utilization: rate grows linearly with utilization
//! - Above optimal utilization: rate grows steeply (incentivizes deposits)
//!
//! All rates are expressed in basis points per block (1 bp = 0.01%).

use serde::{Deserialize, Serialize};

/// Basis points scale factor (10000 = 100%).
pub const BPS_SCALE: u64 = 10_000;

/// Default optimal utilization: 80% (8000 bps).
pub const DEFAULT_OPTIMAL_UTILIZATION: u64 = 8_000;

/// Default base rate: 2% annualized, expressed per-block.
/// Assuming ~7200 blocks/day, ~2.6M blocks/year: 200 bps / 2_600_000 ~ 0.
/// For simplicity we use per-block rate in bps-per-million (microbps).
/// Actual rate_per_block = base_rate_bps * total_supply / BPS_SCALE.
pub const DEFAULT_BASE_RATE_BPS: u64 = 200;

/// Default slope below optimal utilization: 4% at optimal.
pub const DEFAULT_SLOPE1_BPS: u64 = 400;

/// Default slope above optimal utilization: 75% extra at 100%.
pub const DEFAULT_SLOPE2_BPS: u64 = 7_500;

/// Interest rate model with a utilization kink.
///
/// Below `optimal_utilization`: rate = base_rate + utilization * slope1 / optimal
/// Above `optimal_utilization`: rate = base_rate + slope1 + (utilization - optimal) * slope2 / (1 - optimal)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InterestRateModel {
    /// Base borrow rate in basis points (applied at 0% utilization).
    pub base_rate_bps: u64,
    /// Rate increase from 0 to optimal utilization (in bps).
    pub slope1_bps: u64,
    /// Rate increase from optimal to 100% utilization (in bps).
    pub slope2_bps: u64,
    /// Optimal utilization ratio in basis points (e.g., 8000 = 80%).
    pub optimal_utilization_bps: u64,
}

impl Default for InterestRateModel {
    fn default() -> Self {
        Self {
            base_rate_bps: DEFAULT_BASE_RATE_BPS,
            slope1_bps: DEFAULT_SLOPE1_BPS,
            slope2_bps: DEFAULT_SLOPE2_BPS,
            optimal_utilization_bps: DEFAULT_OPTIMAL_UTILIZATION,
        }
    }
}

impl InterestRateModel {
    /// Create a new interest rate model with custom parameters.
    pub fn new(
        base_rate_bps: u64,
        slope1_bps: u64,
        slope2_bps: u64,
        optimal_utilization_bps: u64,
    ) -> Self {
        Self {
            base_rate_bps,
            slope1_bps,
            slope2_bps,
            optimal_utilization_bps,
        }
    }

    /// Compute the current utilization ratio in basis points.
    ///
    /// utilization = total_borrows / total_supply * BPS_SCALE
    /// Returns 0 if total_supply is 0.
    pub fn utilization_bps(&self, total_supply: u64, total_borrows: u64) -> u64 {
        if total_supply == 0 {
            return 0;
        }
        // Avoid overflow: borrows * BPS_SCALE / supply
        (total_borrows as u128 * BPS_SCALE as u128 / total_supply as u128) as u64
    }

    /// Compute the borrow rate in basis points given current utilization.
    ///
    /// Returns the annualized borrow rate in bps.
    pub fn borrow_rate_bps(&self, utilization_bps: u64) -> u64 {
        if utilization_bps <= self.optimal_utilization_bps {
            // Linear portion below kink
            let variable = if self.optimal_utilization_bps == 0 {
                0
            } else {
                self.slope1_bps * utilization_bps / self.optimal_utilization_bps
            };
            self.base_rate_bps + variable
        } else {
            // Steep portion above kink
            let excess = utilization_bps - self.optimal_utilization_bps;
            let denominator = BPS_SCALE - self.optimal_utilization_bps;
            let steep = if denominator == 0 {
                self.slope2_bps
            } else {
                self.slope2_bps * excess / denominator
            };
            self.base_rate_bps + self.slope1_bps + steep
        }
    }

    /// Compute the supply rate in basis points.
    ///
    /// supply_rate = borrow_rate * utilization (suppliers share borrow interest).
    pub fn supply_rate_bps(&self, utilization_bps: u64) -> u64 {
        let borrow_rate = self.borrow_rate_bps(utilization_bps);
        // supply_rate = borrow_rate * utilization / BPS_SCALE
        (borrow_rate as u128 * utilization_bps as u128 / BPS_SCALE as u128) as u64
    }

    /// Accrue interest over a number of blocks.
    ///
    /// Uses simple interest approximation for efficiency:
    /// `accrued = principal * rate_bps * num_blocks / (BPS_SCALE * blocks_per_year)`
    ///
    /// Returns the interest amount accrued.
    pub fn accrue_interest(
        &self,
        principal: u64,
        utilization_bps: u64,
        num_blocks: u64,
        blocks_per_year: u64,
    ) -> u64 {
        let rate = self.borrow_rate_bps(utilization_bps);
        // interest = principal * rate * blocks / (BPS_SCALE * blocks_per_year)
        let numerator = principal as u128 * rate as u128 * num_blocks as u128;
        let denominator = BPS_SCALE as u128 * blocks_per_year as u128;
        if denominator == 0 {
            return 0;
        }
        (numerator / denominator) as u64
    }
}

/// Record of accrued interest for a market, used for temporal proofs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AccrualRecord {
    /// Block height at which this accrual was computed.
    pub block_height: u64,
    /// Cumulative borrow index (scaled by 1e18 for precision).
    /// Starts at 1e18 and grows as interest accrues.
    pub borrow_index: u128,
    /// The borrow rate at this point (bps).
    pub borrow_rate_bps: u64,
    /// Utilization at this point (bps).
    pub utilization_bps: u64,
}

/// Blocks per year constant (assuming 12-second blocks like Ethereum).
pub const BLOCKS_PER_YEAR: u64 = 2_628_000;

/// Index precision: 1e18.
pub const INDEX_PRECISION: u128 = 1_000_000_000_000_000_000;

/// Compute a new borrow index after accruing interest for a period.
///
/// new_index = old_index * (1 + rate_bps * blocks / (BPS_SCALE * blocks_per_year))
pub fn compute_new_borrow_index(
    old_index: u128,
    rate_bps: u64,
    num_blocks: u64,
    blocks_per_year: u64,
) -> u128 {
    let interest_factor = rate_bps as u128 * num_blocks as u128 * INDEX_PRECISION
        / (BPS_SCALE as u128 * blocks_per_year as u128);
    old_index + old_index * interest_factor / INDEX_PRECISION
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_utilization_zero_supply() {
        let model = InterestRateModel::default();
        assert_eq!(model.utilization_bps(0, 0), 0);
    }

    #[test]
    fn test_utilization_no_borrows() {
        let model = InterestRateModel::default();
        assert_eq!(model.utilization_bps(1_000_000, 0), 0);
    }

    #[test]
    fn test_utilization_half() {
        let model = InterestRateModel::default();
        assert_eq!(model.utilization_bps(1_000_000, 500_000), 5_000);
    }

    #[test]
    fn test_utilization_full() {
        let model = InterestRateModel::default();
        assert_eq!(model.utilization_bps(1_000_000, 1_000_000), 10_000);
    }

    #[test]
    fn test_borrow_rate_at_zero() {
        let model = InterestRateModel::default();
        assert_eq!(model.borrow_rate_bps(0), DEFAULT_BASE_RATE_BPS);
    }

    #[test]
    fn test_borrow_rate_at_optimal() {
        let model = InterestRateModel::default();
        let rate = model.borrow_rate_bps(DEFAULT_OPTIMAL_UTILIZATION);
        assert_eq!(rate, DEFAULT_BASE_RATE_BPS + DEFAULT_SLOPE1_BPS);
    }

    #[test]
    fn test_borrow_rate_above_optimal() {
        let model = InterestRateModel::default();
        // At 90% utilization (9000 bps), we're 1000 bps above optimal (8000)
        // excess = 1000, denominator = 10000 - 8000 = 2000
        // steep = 7500 * 1000 / 2000 = 3750
        let rate = model.borrow_rate_bps(9_000);
        assert_eq!(rate, DEFAULT_BASE_RATE_BPS + DEFAULT_SLOPE1_BPS + 3_750);
    }

    #[test]
    fn test_borrow_rate_at_full() {
        let model = InterestRateModel::default();
        let rate = model.borrow_rate_bps(BPS_SCALE);
        assert_eq!(
            rate,
            DEFAULT_BASE_RATE_BPS + DEFAULT_SLOPE1_BPS + DEFAULT_SLOPE2_BPS
        );
    }

    #[test]
    fn test_supply_rate_zero_utilization() {
        let model = InterestRateModel::default();
        assert_eq!(model.supply_rate_bps(0), 0);
    }

    #[test]
    fn test_supply_rate_proportional() {
        let model = InterestRateModel::default();
        let util = 5_000; // 50%
        let borrow_rate = model.borrow_rate_bps(util);
        let supply_rate = model.supply_rate_bps(util);
        // supply_rate = borrow_rate * 50%
        assert_eq!(supply_rate, borrow_rate * util / BPS_SCALE);
    }

    #[test]
    fn test_accrue_interest_basic() {
        let model = InterestRateModel::default();
        let principal = 1_000_000;
        let util = 5_000; // 50%
        let blocks = BLOCKS_PER_YEAR; // One full year
        let interest = model.accrue_interest(principal, util, blocks, BLOCKS_PER_YEAR);
        // At 50% utilization: rate = 200 + 400 * 5000 / 8000 = 200 + 250 = 450 bps
        // interest = 1_000_000 * 450 / 10_000 = 45_000
        assert_eq!(interest, 45_000);
    }

    #[test]
    fn test_utilization_increases_rate() {
        let model = InterestRateModel::default();
        let rate_low = model.borrow_rate_bps(2_000);
        let rate_mid = model.borrow_rate_bps(5_000);
        let rate_high = model.borrow_rate_bps(9_000);
        assert!(rate_low < rate_mid);
        assert!(rate_mid < rate_high);
    }

    #[test]
    fn test_borrow_index_computation() {
        let old_index = INDEX_PRECISION; // Start at 1.0
        let rate_bps = 500; // 5%
        let blocks = BLOCKS_PER_YEAR; // One year
        let new_index = compute_new_borrow_index(old_index, rate_bps, blocks, BLOCKS_PER_YEAR);
        // Should be approximately 1.05 * 1e18
        let expected = INDEX_PRECISION + INDEX_PRECISION * 500 / BPS_SCALE as u128;
        assert_eq!(new_index, expected);
    }
}
