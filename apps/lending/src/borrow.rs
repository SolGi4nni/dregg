//! Borrow positions: take loans against collateral.
//!
//! A borrow position represents a debt backed by collateral deposited in the pool.
//! The borrower must maintain a health factor above the liquidation threshold or
//! risk having their collateral liquidated.

use pyana_types::CellId;
use serde::{Deserialize, Serialize};

use crate::interest::{BLOCKS_PER_YEAR, BPS_SCALE, InterestRateModel};

/// Default liquidation threshold: 80% (collateral must be worth at least
/// 125% of the debt, i.e. LTV of 80%).
pub const DEFAULT_LIQUIDATION_THRESHOLD_BPS: u64 = 8_000;

/// Default liquidation bonus: 5% (liquidator receives 5% extra collateral).
pub const DEFAULT_LIQUIDATION_BONUS_BPS: u64 = 500;

/// Minimum health factor (in bps): 10000 = 1.0. Below this triggers liquidation.
pub const HEALTH_FACTOR_ONE: u64 = BPS_SCALE;

/// A borrow position representing a debt in the lending pool.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BorrowPosition {
    /// Unique position ID.
    pub id: [u8; 32],
    /// The borrower's cell identity.
    pub borrower: CellId,
    /// Asset type being borrowed.
    pub borrow_asset_id: u64,
    /// Principal amount borrowed (in base units).
    pub principal: u64,
    /// The borrow index at time of borrowing (for computing accrued interest).
    pub borrow_index_at_open: u128,
    /// Block height at which the borrow was initiated.
    pub borrowed_at: u64,
    /// Last block at which interest was accrued on this position.
    pub last_accrual_block: u64,
    /// Accrued interest on the debt.
    pub accrued_interest: u64,
    /// Collateral backing this loan.
    pub collateral: Vec<CollateralEntry>,
    /// Liquidation threshold for this position (in bps).
    pub liquidation_threshold_bps: u64,
    /// Whether this position has been fully repaid.
    pub repaid: bool,
    /// Whether this position has been liquidated.
    pub liquidated: bool,
}

/// A single collateral entry backing a borrow position.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CollateralEntry {
    /// Asset type of the collateral.
    pub asset_id: u64,
    /// Amount of collateral deposited.
    pub amount: u64,
    /// Price of the collateral asset (in base denomination per unit).
    /// Updated by oracle feeds.
    pub price: u64,
}

impl BorrowPosition {
    /// Create a new borrow position.
    pub fn new(
        borrower: CellId,
        borrow_asset_id: u64,
        principal: u64,
        collateral: Vec<CollateralEntry>,
        current_borrow_index: u128,
        block_height: u64,
        liquidation_threshold_bps: u64,
    ) -> Self {
        let id = compute_borrow_position_id(&borrower, borrow_asset_id, principal, block_height);
        Self {
            id,
            borrower,
            borrow_asset_id,
            principal,
            borrow_index_at_open: current_borrow_index,
            borrowed_at: block_height,
            last_accrual_block: block_height,
            accrued_interest: 0,
            collateral,
            liquidation_threshold_bps,
            repaid: false,
            liquidated: false,
        }
    }

    /// Get the total debt (principal + accrued interest).
    pub fn total_debt(&self) -> u64 {
        self.principal + self.accrued_interest
    }

    /// Get the total debt using the borrow index for precise calculation.
    pub fn total_debt_with_index(&self, current_borrow_index: u128) -> u64 {
        if self.borrow_index_at_open == 0 {
            return self.principal;
        }
        (self.principal as u128 * current_borrow_index / self.borrow_index_at_open) as u64
    }

    /// Compute the total collateral value (sum of amount * price for each entry).
    pub fn collateral_value(&self) -> u64 {
        self.collateral
            .iter()
            .map(|c| (c.amount as u128 * c.price as u128 / BPS_SCALE as u128) as u64)
            .sum()
    }

    /// Compute the health factor in basis points.
    ///
    /// health_factor = collateral_value * liquidation_threshold / total_debt
    ///
    /// Returns u64::MAX if debt is zero (infinitely healthy).
    /// A health factor below 10000 (1.0) means the position is liquidatable.
    pub fn health_factor_bps(&self) -> u64 {
        let debt = self.total_debt();
        if debt == 0 {
            return u64::MAX;
        }
        let col_value = self.collateral_value();
        // health = col_value * threshold / debt
        (col_value as u128 * self.liquidation_threshold_bps as u128 / debt as u128) as u64
    }

    /// Check if this position is healthy (health factor >= 1.0).
    pub fn is_healthy(&self) -> bool {
        self.health_factor_bps() >= HEALTH_FACTOR_ONE
    }

    /// Accrue interest on the debt.
    pub fn accrue(&mut self, current_block: u64, utilization_bps: u64, model: &InterestRateModel) {
        if current_block <= self.last_accrual_block {
            return;
        }
        let blocks_elapsed = current_block - self.last_accrual_block;
        let borrow_rate = model.borrow_rate_bps(utilization_bps);
        let current_debt = self.total_debt();
        let new_interest = current_debt as u128 * borrow_rate as u128 * blocks_elapsed as u128
            / (BPS_SCALE as u128 * BLOCKS_PER_YEAR as u128);
        self.accrued_interest += new_interest as u64;
        self.last_accrual_block = current_block;
    }

    /// Repay a portion of the debt.
    ///
    /// Returns the actual amount applied (cannot repay more than total debt).
    pub fn repay(&mut self, amount: u64) -> u64 {
        if self.repaid || self.liquidated {
            return 0;
        }
        let debt = self.total_debt();
        let actual = amount.min(debt);
        // Pay off interest first, then principal
        if actual <= self.accrued_interest {
            self.accrued_interest -= actual;
        } else {
            let principal_payment = actual - self.accrued_interest;
            self.accrued_interest = 0;
            self.principal -= principal_payment;
        }
        if self.principal == 0 && self.accrued_interest == 0 {
            self.repaid = true;
        }
        actual
    }

    /// Add additional collateral to the position.
    pub fn add_collateral(&mut self, entry: CollateralEntry) {
        // Merge with existing entry for same asset if possible
        if let Some(existing) = self
            .collateral
            .iter_mut()
            .find(|c| c.asset_id == entry.asset_id)
        {
            existing.amount += entry.amount;
            existing.price = entry.price; // Update price
        } else {
            self.collateral.push(entry);
        }
    }

    /// Update oracle prices for collateral.
    pub fn update_prices(&mut self, price_updates: &[(u64, u64)]) {
        for (asset_id, new_price) in price_updates {
            if let Some(entry) = self.collateral.iter_mut().find(|c| c.asset_id == *asset_id) {
                entry.price = *new_price;
            }
        }
    }
}

/// Compute a deterministic borrow position ID.
pub fn compute_borrow_position_id(
    borrower: &CellId,
    asset_id: u64,
    principal: u64,
    block_height: u64,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-lending-borrow-position-v1");
    hasher.update(borrower.as_bytes());
    hasher.update(&asset_id.to_le_bytes());
    hasher.update(&principal.to_le_bytes());
    hasher.update(&block_height.to_le_bytes());
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interest::INDEX_PRECISION;

    fn test_borrower() -> CellId {
        CellId([0xBB; 32])
    }

    fn test_collateral() -> Vec<CollateralEntry> {
        vec![CollateralEntry {
            asset_id: 2,
            amount: 1_500_000,
            // price = 10000 means 1:1 in BPS_SCALE denomination
            price: BPS_SCALE,
        }]
    }

    #[test]
    fn test_create_borrow_position() {
        let pos = BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            test_collateral(),
            INDEX_PRECISION,
            100,
            DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        );
        assert_eq!(pos.principal, 1_000_000);
        assert_eq!(pos.total_debt(), 1_000_000);
        assert!(!pos.repaid);
        assert!(!pos.liquidated);
    }

    #[test]
    fn test_collateral_value() {
        let pos = BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            test_collateral(),
            INDEX_PRECISION,
            100,
            DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        );
        // 1_500_000 * 10000 / 10000 = 1_500_000
        assert_eq!(pos.collateral_value(), 1_500_000);
    }

    #[test]
    fn test_health_factor_healthy() {
        let pos = BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            test_collateral(),
            INDEX_PRECISION,
            100,
            DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        );
        // health = 1_500_000 * 8000 / 1_000_000 = 12000 bps (1.2)
        assert_eq!(pos.health_factor_bps(), 12_000);
        assert!(pos.is_healthy());
    }

    #[test]
    fn test_health_factor_unhealthy() {
        let collateral = vec![CollateralEntry {
            asset_id: 2,
            amount: 1_000_000,
            price: BPS_SCALE,
        }];
        let mut pos = BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            collateral,
            INDEX_PRECISION,
            100,
            DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        );
        // Simulate price drop: collateral now worth half
        pos.update_prices(&[(2, BPS_SCALE / 2)]);
        // health = 500_000 * 8000 / 1_000_000 = 4000 bps (0.4)
        assert_eq!(pos.health_factor_bps(), 4_000);
        assert!(!pos.is_healthy());
    }

    #[test]
    fn test_accrue_interest() {
        let model = InterestRateModel::default();
        let mut pos = BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            test_collateral(),
            INDEX_PRECISION,
            0,
            DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        );
        // Accrue for one year at 50% utilization
        pos.accrue(BLOCKS_PER_YEAR, 5_000, &model);
        // borrow_rate at 50%: 200 + 400 * 5000 / 8000 = 450 bps
        // interest = 1_000_000 * 450 / 10_000 = 45_000
        assert_eq!(pos.accrued_interest, 45_000);
        assert_eq!(pos.total_debt(), 1_045_000);
    }

    #[test]
    fn test_repay_partial() {
        let mut pos = BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            test_collateral(),
            INDEX_PRECISION,
            100,
            DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        );
        pos.accrued_interest = 50_000;
        let repaid = pos.repay(70_000);
        assert_eq!(repaid, 70_000);
        assert_eq!(pos.accrued_interest, 0);
        assert_eq!(pos.principal, 980_000);
        assert!(!pos.repaid);
    }

    #[test]
    fn test_repay_full() {
        let mut pos = BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            test_collateral(),
            INDEX_PRECISION,
            100,
            DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        );
        pos.accrued_interest = 50_000;
        let repaid = pos.repay(1_050_000);
        assert_eq!(repaid, 1_050_000);
        assert!(pos.repaid);
        assert_eq!(pos.total_debt(), 0);
    }

    #[test]
    fn test_repay_excess() {
        let mut pos = BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            test_collateral(),
            INDEX_PRECISION,
            100,
            DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        );
        // Try to repay more than owed
        let repaid = pos.repay(2_000_000);
        assert_eq!(repaid, 1_000_000); // Capped at total debt
        assert!(pos.repaid);
    }

    #[test]
    fn test_add_collateral() {
        let mut pos = BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            test_collateral(),
            INDEX_PRECISION,
            100,
            DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        );
        pos.add_collateral(CollateralEntry {
            asset_id: 2,
            amount: 500_000,
            price: BPS_SCALE,
        });
        // Should merge with existing asset_id=2 entry
        assert_eq!(pos.collateral.len(), 1);
        assert_eq!(pos.collateral[0].amount, 2_000_000);
    }

    #[test]
    fn test_add_different_collateral() {
        let mut pos = BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            test_collateral(),
            INDEX_PRECISION,
            100,
            DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        );
        pos.add_collateral(CollateralEntry {
            asset_id: 3,
            amount: 500_000,
            price: BPS_SCALE * 2,
        });
        assert_eq!(pos.collateral.len(), 2);
    }

    #[test]
    fn test_health_factor_zero_debt() {
        let mut pos = BorrowPosition::new(
            test_borrower(),
            1,
            1_000_000,
            test_collateral(),
            INDEX_PRECISION,
            100,
            DEFAULT_LIQUIDATION_THRESHOLD_BPS,
        );
        pos.repay(1_000_000);
        assert_eq!(pos.health_factor_bps(), u64::MAX);
    }
}
