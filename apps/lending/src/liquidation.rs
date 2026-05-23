//! Liquidation engine: health checks and liquidation execution.
//!
//! When a borrow position's health factor drops below 1.0, anyone can trigger
//! a liquidation. The liquidator repays a portion of the debt and receives
//! the equivalent collateral value plus a liquidation bonus.
//!
//! This maps to pyana's ConditionalTurn primitive: the liquidation is conditional
//! on the health factor being below threshold.

use pyana_types::CellId;
use serde::{Deserialize, Serialize};

use crate::borrow::{BorrowPosition, DEFAULT_LIQUIDATION_BONUS_BPS, HEALTH_FACTOR_ONE};
use crate::interest::BPS_SCALE;

/// Maximum close factor: liquidator can repay up to 50% of debt in one liquidation.
pub const MAX_CLOSE_FACTOR_BPS: u64 = 5_000;

/// Result of a liquidation attempt.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum LiquidationResult {
    /// Liquidation succeeded.
    Success(LiquidationReceipt),
    /// Position is healthy, liquidation rejected.
    PositionHealthy { health_factor_bps: u64 },
    /// Position already liquidated or repaid.
    PositionClosed,
    /// Liquidation amount exceeds close factor.
    ExceedsCloseFactor { max_repayable: u64, requested: u64 },
}

/// Receipt of a successful liquidation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LiquidationReceipt {
    /// The position that was liquidated.
    pub position_id: [u8; 32],
    /// The liquidator's cell identity.
    pub liquidator: CellId,
    /// Amount of debt repaid by the liquidator.
    pub debt_repaid: u64,
    /// Collateral seized (asset_id, amount).
    pub collateral_seized: Vec<(u64, u64)>,
    /// Bonus collateral awarded to the liquidator.
    pub bonus_amount: u64,
    /// Block height at which liquidation occurred.
    pub liquidated_at: u64,
}

/// The liquidation engine that checks health and executes liquidations.
#[derive(Clone, Debug)]
pub struct LiquidationEngine {
    /// Close factor: max percentage of debt repayable in one liquidation (bps).
    pub close_factor_bps: u64,
    /// Liquidation bonus (bps) — extra collateral awarded to liquidators.
    pub liquidation_bonus_bps: u64,
}

impl Default for LiquidationEngine {
    fn default() -> Self {
        Self {
            close_factor_bps: MAX_CLOSE_FACTOR_BPS,
            liquidation_bonus_bps: DEFAULT_LIQUIDATION_BONUS_BPS,
        }
    }
}

impl LiquidationEngine {
    /// Create a new liquidation engine with custom parameters.
    pub fn new(close_factor_bps: u64, liquidation_bonus_bps: u64) -> Self {
        Self {
            close_factor_bps,
            liquidation_bonus_bps,
        }
    }

    /// Check if a position can be liquidated.
    pub fn can_liquidate(&self, position: &BorrowPosition) -> bool {
        if position.repaid || position.liquidated {
            return false;
        }
        !position.is_healthy()
    }

    /// Compute the maximum debt that can be repaid in a single liquidation.
    pub fn max_liquidation_amount(&self, position: &BorrowPosition) -> u64 {
        let total_debt = position.total_debt();
        (total_debt as u128 * self.close_factor_bps as u128 / BPS_SCALE as u128) as u64
    }

    /// Compute the collateral to seize for a given debt repayment amount.
    ///
    /// collateral_seized = debt_repaid * (1 + bonus) / collateral_price
    /// The bonus incentivizes liquidators.
    pub fn compute_seizure(&self, debt_repaid: u64, collateral_price: u64) -> u64 {
        if collateral_price == 0 {
            return 0;
        }
        // seized_value = debt_repaid * (BPS_SCALE + bonus) / BPS_SCALE
        let seized_value = debt_repaid as u128 * (BPS_SCALE + self.liquidation_bonus_bps) as u128
            / BPS_SCALE as u128;
        // Convert value to collateral units: seized_amount = seized_value * BPS_SCALE / price
        (seized_value * BPS_SCALE as u128 / collateral_price as u128) as u64
    }

    /// Execute a liquidation.
    ///
    /// The liquidator specifies how much debt they want to repay and which
    /// collateral asset they want to receive.
    pub fn liquidate(
        &self,
        position: &mut BorrowPosition,
        liquidator: CellId,
        repay_amount: u64,
        collateral_asset_id: u64,
        current_block: u64,
    ) -> LiquidationResult {
        // Check position is closed
        if position.repaid || position.liquidated {
            return LiquidationResult::PositionClosed;
        }

        // Check health factor
        let health = position.health_factor_bps();
        if health >= HEALTH_FACTOR_ONE {
            return LiquidationResult::PositionHealthy {
                health_factor_bps: health,
            };
        }

        // Check close factor
        let max_repay = self.max_liquidation_amount(position);
        if repay_amount > max_repay {
            return LiquidationResult::ExceedsCloseFactor {
                max_repayable: max_repay,
                requested: repay_amount,
            };
        }

        // Find the collateral entry
        let collateral_entry = match position
            .collateral
            .iter()
            .find(|c| c.asset_id == collateral_asset_id)
        {
            Some(e) => e.clone(),
            None => {
                return LiquidationResult::PositionClosed;
            }
        };

        // Compute seizure
        let seized_amount = self.compute_seizure(repay_amount, collateral_entry.price);
        let actual_seized = seized_amount.min(collateral_entry.amount);

        // Compute bonus portion
        let base_seized = repay_amount as u128 * BPS_SCALE as u128 / collateral_entry.price as u128;
        let bonus_amount = actual_seized.saturating_sub(base_seized as u64);

        // Apply the liquidation: repay debt
        position.repay(repay_amount);

        // Remove seized collateral
        if let Some(entry) = position
            .collateral
            .iter_mut()
            .find(|c| c.asset_id == collateral_asset_id)
        {
            entry.amount = entry.amount.saturating_sub(actual_seized);
        }

        // If all collateral is gone, mark as liquidated
        let total_collateral: u64 = position.collateral.iter().map(|c| c.amount).sum();
        if total_collateral == 0 || position.total_debt() == 0 {
            position.liquidated = true;
        }

        LiquidationResult::Success(LiquidationReceipt {
            position_id: position.id,
            liquidator,
            debt_repaid: repay_amount,
            collateral_seized: vec![(collateral_asset_id, actual_seized)],
            bonus_amount,
            liquidated_at: current_block,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::borrow::CollateralEntry;
    use crate::interest::INDEX_PRECISION;

    fn test_borrower() -> CellId {
        CellId([0xBB; 32])
    }

    fn test_liquidator() -> CellId {
        CellId([0xCC; 32])
    }

    fn unhealthy_position() -> BorrowPosition {
        let collateral = vec![CollateralEntry {
            asset_id: 2,
            amount: 1_000_000,
            // Price dropped to 80% of initial
            price: BPS_SCALE * 8 / 10,
        }];
        BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            collateral,
            INDEX_PRECISION,
            100,
            crate::borrow::DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        )
    }

    fn healthy_position() -> BorrowPosition {
        let collateral = vec![CollateralEntry {
            asset_id: 2,
            amount: 2_000_000,
            price: BPS_SCALE,
        }];
        BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            collateral,
            INDEX_PRECISION,
            100,
            crate::borrow::DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        )
    }

    #[test]
    fn test_can_liquidate_unhealthy() {
        let engine = LiquidationEngine::default();
        let pos = unhealthy_position();
        assert!(!pos.is_healthy());
        assert!(engine.can_liquidate(&pos));
    }

    #[test]
    fn test_cannot_liquidate_healthy() {
        let engine = LiquidationEngine::default();
        let pos = healthy_position();
        assert!(pos.is_healthy());
        assert!(!engine.can_liquidate(&pos));
    }

    #[test]
    fn test_liquidation_rejected_healthy() {
        let engine = LiquidationEngine::default();
        let mut pos = healthy_position();
        let result = engine.liquidate(&mut pos, test_liquidator(), 100_000, 2, 200);
        assert!(matches!(result, LiquidationResult::PositionHealthy { .. }));
    }

    #[test]
    fn test_liquidation_succeeds() {
        let engine = LiquidationEngine::default();
        let mut pos = unhealthy_position();
        let repay_amount = 400_000; // Within close factor (50% of 1M = 500K)
        let result = engine.liquidate(&mut pos, test_liquidator(), repay_amount, 2, 200);
        match result {
            LiquidationResult::Success(receipt) => {
                assert_eq!(receipt.debt_repaid, 400_000);
                assert_eq!(receipt.liquidator, test_liquidator());
                assert!(!receipt.collateral_seized.is_empty());
                // Liquidator got bonus
                assert!(receipt.bonus_amount > 0);
            }
            other => panic!("Expected Success, got {:?}", other),
        }
    }

    #[test]
    fn test_liquidation_exceeds_close_factor() {
        let engine = LiquidationEngine::default();
        let mut pos = unhealthy_position();
        // Try to repay 60% of debt (exceeds 50% close factor)
        let result = engine.liquidate(&mut pos, test_liquidator(), 600_000, 2, 200);
        assert!(matches!(
            result,
            LiquidationResult::ExceedsCloseFactor { .. }
        ));
    }

    #[test]
    fn test_liquidation_already_repaid() {
        let engine = LiquidationEngine::default();
        let mut pos = unhealthy_position();
        pos.repaid = true;
        let result = engine.liquidate(&mut pos, test_liquidator(), 100_000, 2, 200);
        assert!(matches!(result, LiquidationResult::PositionClosed));
    }

    #[test]
    fn test_compute_seizure_with_bonus() {
        let engine = LiquidationEngine::default();
        // Repay 100_000, collateral price = 10000 (1:1)
        let seized = engine.compute_seizure(100_000, BPS_SCALE);
        // seized_value = 100_000 * 10500 / 10000 = 105_000
        // seized_amount = 105_000 * 10000 / 10000 = 105_000
        assert_eq!(seized, 105_000);
    }

    #[test]
    fn test_max_liquidation_amount() {
        let engine = LiquidationEngine::default();
        let pos = unhealthy_position();
        let max = engine.max_liquidation_amount(&pos);
        // 50% of 1_000_000 = 500_000
        assert_eq!(max, 500_000);
    }
}
