//! Supply positions: deposit tokens to earn interest.
//!
//! A supply position represents a lender's deposit into a lending market.
//! The depositor receives an interest-bearing receipt that tracks their share
//! of the pool. Interest accrues continuously based on utilization.

use pyana_types::CellId;
use serde::{Deserialize, Serialize};

use crate::interest::{BLOCKS_PER_YEAR, InterestRateModel};

/// A supply position representing a deposit in the lending pool.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SupplyPosition {
    /// Unique position ID (BLAKE3 hash of creation params).
    pub id: [u8; 32],
    /// The depositor's cell identity.
    pub supplier: CellId,
    /// Asset type identifier.
    pub asset_id: u64,
    /// Principal amount deposited (in base units).
    pub principal: u64,
    /// The borrow index at the time of deposit (for computing earned interest).
    pub deposit_index: u128,
    /// Block height at which the deposit was made.
    pub deposited_at: u64,
    /// Block height of last interest accrual.
    pub last_accrual_block: u64,
    /// Accumulated interest earned (in base units).
    pub accrued_interest: u64,
    /// Whether this position has been withdrawn.
    pub withdrawn: bool,
}

impl SupplyPosition {
    /// Create a new supply position.
    pub fn new(
        supplier: CellId,
        asset_id: u64,
        principal: u64,
        current_borrow_index: u128,
        block_height: u64,
    ) -> Self {
        let id = compute_supply_position_id(&supplier, asset_id, principal, block_height);
        Self {
            id,
            supplier,
            asset_id,
            principal,
            deposit_index: current_borrow_index,
            deposited_at: block_height,
            last_accrual_block: block_height,
            accrued_interest: 0,
            withdrawn: false,
        }
    }

    /// Compute the current balance including accrued interest.
    pub fn current_balance(&self, current_borrow_index: u128) -> u64 {
        if self.deposit_index == 0 {
            return self.principal;
        }
        // balance = principal * current_index / deposit_index
        let balance = self.principal as u128 * current_borrow_index / self.deposit_index;
        balance as u64
    }

    /// Accrue interest to this position based on the current market state.
    ///
    /// Updates `accrued_interest` and `last_accrual_block`.
    pub fn accrue(&mut self, current_block: u64, utilization_bps: u64, model: &InterestRateModel) {
        if current_block <= self.last_accrual_block {
            return;
        }
        let blocks_elapsed = current_block - self.last_accrual_block;
        let supply_rate = model.supply_rate_bps(utilization_bps);
        let current_balance = self.principal + self.accrued_interest;
        let new_interest = current_balance as u128 * supply_rate as u128 * blocks_elapsed as u128
            / (crate::interest::BPS_SCALE as u128 * BLOCKS_PER_YEAR as u128);
        self.accrued_interest += new_interest as u64;
        self.last_accrual_block = current_block;
    }

    /// Withdraw the full position (principal + interest).
    ///
    /// Returns the total withdrawal amount, or None if already withdrawn.
    pub fn withdraw(&mut self) -> Option<u64> {
        if self.withdrawn {
            return None;
        }
        self.withdrawn = true;
        Some(self.principal + self.accrued_interest)
    }

    /// Withdraw a partial amount from the position.
    ///
    /// Returns the actual amount withdrawn, or None if already fully withdrawn.
    pub fn withdraw_partial(&mut self, amount: u64) -> Option<u64> {
        if self.withdrawn {
            return None;
        }
        let total = self.principal + self.accrued_interest;
        let actual = amount.min(total);
        if actual >= total {
            self.withdrawn = true;
        } else if actual <= self.accrued_interest {
            self.accrued_interest -= actual;
        } else {
            let from_principal = actual - self.accrued_interest;
            self.accrued_interest = 0;
            self.principal -= from_principal;
        }
        Some(actual)
    }
}

/// Compute a deterministic supply position ID.
pub fn compute_supply_position_id(
    supplier: &CellId,
    asset_id: u64,
    principal: u64,
    block_height: u64,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-lending-supply-position-v1");
    hasher.update(supplier.as_bytes());
    hasher.update(&asset_id.to_le_bytes());
    hasher.update(&principal.to_le_bytes());
    hasher.update(&block_height.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// A receipt token proving a supply position exists.
///
/// This is the interest-bearing receipt that the supplier holds.
/// It can be presented to withdraw the position (principal + accrued interest).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SupplyReceipt {
    /// The position ID this receipt corresponds to.
    pub position_id: [u8; 32],
    /// The supplier who owns this receipt.
    pub supplier: CellId,
    /// Asset deposited.
    pub asset_id: u64,
    /// Original principal.
    pub principal: u64,
    /// Borrow index at time of deposit.
    pub deposit_index: u128,
    /// Block height of deposit.
    pub deposited_at: u64,
}

impl SupplyReceipt {
    /// Create a receipt from a supply position.
    pub fn from_position(position: &SupplyPosition) -> Self {
        Self {
            position_id: position.id,
            supplier: position.supplier,
            asset_id: position.asset_id,
            principal: position.principal,
            deposit_index: position.deposit_index,
            deposited_at: position.deposited_at,
        }
    }

    /// Compute the current value of this receipt given the current borrow index.
    pub fn current_value(&self, current_borrow_index: u128) -> u64 {
        if self.deposit_index == 0 {
            return self.principal;
        }
        (self.principal as u128 * current_borrow_index / self.deposit_index) as u64
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interest::{INDEX_PRECISION, InterestRateModel};

    fn test_supplier() -> CellId {
        CellId([0xAA; 32])
    }

    #[test]
    fn test_create_supply_position() {
        let pos = SupplyPosition::new(test_supplier(), 1, 1_000_000, INDEX_PRECISION, 100);
        assert_eq!(pos.principal, 1_000_000);
        assert_eq!(pos.deposit_index, INDEX_PRECISION);
        assert_eq!(pos.deposited_at, 100);
        assert_eq!(pos.accrued_interest, 0);
        assert!(!pos.withdrawn);
    }

    #[test]
    fn test_current_balance_no_interest() {
        let pos = SupplyPosition::new(test_supplier(), 1, 1_000_000, INDEX_PRECISION, 100);
        assert_eq!(pos.current_balance(INDEX_PRECISION), 1_000_000);
    }

    #[test]
    fn test_current_balance_with_interest() {
        let pos = SupplyPosition::new(test_supplier(), 1, 1_000_000, INDEX_PRECISION, 100);
        // Index grew by 5%
        let new_index = INDEX_PRECISION + INDEX_PRECISION / 20;
        assert_eq!(pos.current_balance(new_index), 1_050_000);
    }

    #[test]
    fn test_accrue_interest() {
        let model = InterestRateModel::default();
        let mut pos = SupplyPosition::new(test_supplier(), 1, 1_000_000, INDEX_PRECISION, 0);
        // Accrue for one year at 50% utilization
        pos.accrue(BLOCKS_PER_YEAR, 5_000, &model);
        // supply_rate at 50% util: borrow_rate * util / BPS_SCALE
        // borrow_rate at 50%: 200 + 400 * 5000 / 8000 = 450 bps
        // supply_rate = 450 * 5000 / 10000 = 225 bps
        // interest = 1_000_000 * 225 / 10_000 = 22_500
        assert_eq!(pos.accrued_interest, 22_500);
    }

    #[test]
    fn test_withdraw_full() {
        let mut pos = SupplyPosition::new(test_supplier(), 1, 1_000_000, INDEX_PRECISION, 0);
        pos.accrued_interest = 50_000;
        let amount = pos.withdraw();
        assert_eq!(amount, Some(1_050_000));
        assert!(pos.withdrawn);
        // Cannot withdraw again
        assert_eq!(pos.withdraw(), None);
    }

    #[test]
    fn test_withdraw_partial() {
        let mut pos = SupplyPosition::new(test_supplier(), 1, 1_000_000, INDEX_PRECISION, 0);
        pos.accrued_interest = 50_000;
        let amount = pos.withdraw_partial(30_000);
        assert_eq!(amount, Some(30_000));
        assert_eq!(pos.accrued_interest, 20_000);
        assert_eq!(pos.principal, 1_000_000);
        assert!(!pos.withdrawn);
    }

    #[test]
    fn test_supply_receipt() {
        let pos = SupplyPosition::new(test_supplier(), 1, 1_000_000, INDEX_PRECISION, 100);
        let receipt = SupplyReceipt::from_position(&pos);
        assert_eq!(receipt.position_id, pos.id);
        assert_eq!(receipt.current_value(INDEX_PRECISION), 1_000_000);
        // 10% interest accrued
        let grown_index = INDEX_PRECISION + INDEX_PRECISION / 10;
        assert_eq!(receipt.current_value(grown_index), 1_100_000);
    }
}
