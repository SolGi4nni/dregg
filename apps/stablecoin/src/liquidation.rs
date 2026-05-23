//! Liquidation engine: monitors CDPs and executes liquidations.
//!
//! When a CDP's collateral ratio drops below the minimum threshold (typically 150%),
//! anyone can trigger liquidation. The liquidator:
//! 1. Pays off the position's debt (burns stablecoins)
//! 2. Receives the collateral (at a discount — the liquidation bonus)
//! 3. The position is marked as liquidated
//!
//! # Incentive Structure
//!
//! - Liquidation bonus (default 5%): liquidator receives collateral worth
//!   `debt * (1 + bonus_bps/10000)` from the position's collateral.
//! - Remaining collateral (if any) is returned to the position owner.
//! - This creates a race among liquidators, ensuring positions are liquidated quickly.

use pyana_cell::{CellId, Note};

use crate::cdp::{CollateralPosition, PUSD_ASSET_TYPE, PositionStatus, StablecoinRegistry};

/// Default liquidation bonus in basis points (5% = 500 bps).
pub const DEFAULT_LIQUIDATION_BONUS_BPS: u64 = 500;

/// Liquidation engine configuration.
#[derive(Clone, Debug)]
pub struct LiquidationEngine {
    /// Bonus given to liquidators (in bps on top of debt repayment).
    pub bonus_bps: u64,
}

/// Result of a liquidation execution.
#[derive(Clone, Debug)]
pub struct LiquidationResult {
    /// The position that was liquidated.
    pub position_id: [u8; 32],
    /// The liquidator who executed the liquidation.
    pub liquidator: CellId,
    /// Debt that was repaid (burned stablecoins).
    pub debt_repaid: u64,
    /// Collateral seized by the liquidator.
    pub collateral_seized: u64,
    /// Collateral returned to the owner (surplus after covering debt + bonus).
    pub collateral_returned: u64,
    /// The stablecoin notes burned in liquidation.
    pub burned_notes: Vec<Note>,
    /// Collateral notes created for the liquidator.
    pub liquidator_notes: Vec<Note>,
    /// Collateral notes returned to the owner (if surplus exists).
    pub owner_notes: Vec<Note>,
}

/// Errors specific to liquidation operations.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum LiquidationError {
    #[error("position {id:?} is not liquidatable at price {price}")]
    NotLiquidatable { id: [u8; 32], price: u64 },
    #[error("position {id:?} is not active")]
    NotActive { id: [u8; 32] },
    #[error("liquidator has insufficient funds to repay debt {debt}")]
    InsufficientFunds { debt: u64 },
    #[error("oracle error: {0}")]
    Oracle(String),
}

impl LiquidationEngine {
    /// Create a new liquidation engine with the given bonus.
    pub fn new(bonus_bps: u64) -> Self {
        Self { bonus_bps }
    }

    /// Create a liquidation engine with default parameters.
    pub fn default_config() -> Self {
        Self::new(DEFAULT_LIQUIDATION_BONUS_BPS)
    }

    /// Check if a position is liquidatable at the given price.
    pub fn is_liquidatable(&self, position: &CollateralPosition, price: u64) -> bool {
        position.is_liquidatable(price)
    }

    /// Calculate the collateral to seize for a liquidation.
    ///
    /// Returns `(collateral_seized, collateral_returned_to_owner)`.
    pub fn calculate_seizure(&self, position: &CollateralPosition, price: u64) -> (u64, u64) {
        if price == 0 || position.debt_amount == 0 {
            return (0, 0);
        }

        // How much collateral the debt + bonus is worth
        // collateral_needed = debt / price * (1 + bonus_bps / 10000)
        // In integer arithmetic: (debt * (10000 + bonus_bps)) / (price * 10000)
        let numerator = position.debt_amount as u128 * (10000 + self.bonus_bps) as u128;
        let denominator = price as u128 * 10000;
        let collateral_needed = (numerator / denominator) as u64;

        // Cap at available collateral
        let seized = collateral_needed.min(position.collateral_amount);
        let returned = position.collateral_amount.saturating_sub(seized);

        (seized, returned)
    }

    /// Execute a liquidation on an under-collateralized position.
    ///
    /// The liquidator must have enough stablecoins to cover the position's debt.
    pub fn liquidate(
        &self,
        position: &mut CollateralPosition,
        liquidator: CellId,
        price: u64,
        current_height: u64,
    ) -> Result<LiquidationResult, LiquidationError> {
        // Verify position is active
        if position.status != PositionStatus::Active {
            return Err(LiquidationError::NotActive { id: position.id });
        }

        // Verify position is liquidatable
        if !position.is_liquidatable(price) {
            return Err(LiquidationError::NotLiquidatable {
                id: position.id,
                price,
            });
        }

        let debt_repaid = position.debt_amount;
        let (collateral_seized, collateral_returned) = self.calculate_seizure(position, price);

        // Mark position as liquidated
        position.status = PositionStatus::Liquidated {
            liquidated_at: current_height,
            liquidator: liquidator.clone(),
        };
        position.debt_amount = 0;
        position.collateral_amount = 0;

        // Create burn note (stablecoins destroyed)
        let mut burn_nonce = [0u8; 32];
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"liquidation-burn");
        hasher.update(&position.id);
        hasher.update(&current_height.to_le_bytes());
        burn_nonce.copy_from_slice(hasher.finalize().as_bytes());

        let burned_note = Note {
            owner: liquidator.0,
            fields: [PUSD_ASSET_TYPE, debt_repaid, 0, 0, 0, 0, 0, 0],
            randomness: [0u8; 32],
            creation_nonce: burn_nonce,
        };

        // Create collateral note for liquidator
        let mut liq_nonce = [0u8; 32];
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"liquidation-seize");
        hasher.update(&position.id);
        hasher.update(&liquidator.0);
        liq_nonce.copy_from_slice(hasher.finalize().as_bytes());

        let liquidator_note = Note {
            owner: liquidator.0,
            fields: [
                position.collateral_asset,
                collateral_seized,
                0,
                0,
                0,
                0,
                0,
                0,
            ],
            randomness: [0u8; 32],
            creation_nonce: liq_nonce,
        };

        // Create return note for owner (if surplus)
        let owner_notes = if collateral_returned > 0 {
            let mut return_nonce = [0u8; 32];
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"liquidation-return");
            hasher.update(&position.id);
            hasher.update(&position.owner.0);
            return_nonce.copy_from_slice(hasher.finalize().as_bytes());

            vec![Note {
                owner: position.owner.0,
                fields: [
                    position.collateral_asset,
                    collateral_returned,
                    0,
                    0,
                    0,
                    0,
                    0,
                    0,
                ],
                randomness: [0u8; 32],
                creation_nonce: return_nonce,
            }]
        } else {
            vec![]
        };

        Ok(LiquidationResult {
            position_id: position.id,
            liquidator,
            debt_repaid,
            collateral_seized,
            collateral_returned,
            burned_notes: vec![burned_note],
            liquidator_notes: vec![liquidator_note],
            owner_notes,
        })
    }

    /// Scan a registry for liquidatable positions at the current price.
    pub fn scan_liquidatable<'a>(
        &self,
        registry: &'a StablecoinRegistry,
        collateral_asset: u64,
        price: u64,
    ) -> Vec<&'a CollateralPosition> {
        registry.liquidatable_positions(collateral_asset, price)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cdp::ETH_ASSET_TYPE;
    use crate::circuit::MIN_RATIO_BPS;

    fn test_owner() -> CellId {
        CellId([0xAA; 32])
    }

    fn test_liquidator() -> CellId {
        CellId([0xBB; 32])
    }

    #[test]
    fn liquidation_seizure_calculation() {
        let engine = LiquidationEngine::default_config();
        let mut position = CollateralPosition::open(
            test_owner(),
            1000, // 1000 units of collateral
            ETH_ASSET_TYPE,
            MIN_RATIO_BPS,
            100,
        )
        .unwrap();
        position.debt_amount = 100_000; // 100k debt

        // Price = 50 => collateral_value = 50_000 (under 150% of 100k)
        // Seizure: debt=100_000, bonus=5% => 105_000 / 50 = 2100 needed
        // But only 1000 available => seize all 1000
        let (seized, returned) = engine.calculate_seizure(&position, 50);
        assert_eq!(seized, 1000); // Capped at available
        assert_eq!(returned, 0);

        // Price = 200 => collateral_value = 200_000, ratio = 200% (NOT liquidatable)
        // But let's calculate seizure anyway for testing
        // Seizure: 100_000 * 10500 / (200 * 10000) = 1_050_000_000 / 2_000_000 = 525
        let (seized, returned) = engine.calculate_seizure(&position, 200);
        assert_eq!(seized, 525);
        assert_eq!(returned, 475);
    }

    #[test]
    fn liquidation_execution() {
        let engine = LiquidationEngine::default_config();
        let mut position =
            CollateralPosition::open(test_owner(), 1000, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
                .unwrap();
        position.debt_amount = 100_000;

        // At price=50, ratio = 1000*50*10000/100_000 = 5000 bps = 50% < 150%
        assert!(position.is_liquidatable(50));

        let result = engine
            .liquidate(&mut position, test_liquidator(), 50, 200)
            .unwrap();

        assert_eq!(result.debt_repaid, 100_000);
        assert_eq!(result.collateral_seized, 1000); // all seized (insufficient to cover debt+bonus)
        assert_eq!(result.collateral_returned, 0);
        assert_eq!(
            position.status,
            PositionStatus::Liquidated {
                liquidated_at: 200,
                liquidator: test_liquidator(),
            }
        );
        assert_eq!(position.debt_amount, 0);
        assert_eq!(position.collateral_amount, 0);
    }

    #[test]
    fn healthy_position_not_liquidatable() {
        let engine = LiquidationEngine::default_config();
        let mut position =
            CollateralPosition::open(test_owner(), 1000, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
                .unwrap();
        position.debt_amount = 100_000;

        // At price=200, ratio = 200% > 150%
        assert!(!position.is_liquidatable(200));

        let result = engine.liquidate(&mut position, test_liquidator(), 200, 200);
        assert!(matches!(
            result,
            Err(LiquidationError::NotLiquidatable { .. })
        ));
    }

    #[test]
    fn liquidation_with_surplus() {
        let engine = LiquidationEngine::default_config();
        let mut position = CollateralPosition::open(
            test_owner(),
            10_000, // Lots of collateral
            ETH_ASSET_TYPE,
            MIN_RATIO_BPS,
            100,
        )
        .unwrap();
        position.debt_amount = 1_000_000; // 1M debt

        // Price = 140 => collateral_value = 1_400_000, ratio = 14000 bps = 140% < 150%
        assert!(position.is_liquidatable(140));

        let result = engine
            .liquidate(&mut position, test_liquidator(), 140, 200)
            .unwrap();

        // Seizure: 1_000_000 * 10500 / (140 * 10000) = 10_500_000_000 / 1_400_000 = 7500
        assert_eq!(result.collateral_seized, 7500);
        assert_eq!(result.collateral_returned, 2500);
        assert_eq!(result.owner_notes.len(), 1);
        assert_eq!(result.owner_notes[0].fields[1], 2500);
    }

    #[test]
    fn registry_scan() {
        let engine = LiquidationEngine::default_config();
        let mut registry = StablecoinRegistry::new();

        let mut p1 =
            CollateralPosition::open(test_owner(), 1000, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
                .unwrap();
        p1.debt_amount = 100_000;

        let mut p2 =
            CollateralPosition::open(CellId([0xCC; 32]), 5000, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
                .unwrap();
        p2.debt_amount = 100_000;

        registry.register(p1);
        registry.register(p2);

        // At price=50: p1 ratio=50%, p2 ratio=250%
        let liquidatable = engine.scan_liquidatable(&registry, ETH_ASSET_TYPE, 50);
        assert_eq!(liquidatable.len(), 1);

        // At price=10: both under-collateralized
        let liquidatable = engine.scan_liquidatable(&registry, ETH_ASSET_TYPE, 10);
        assert_eq!(liquidatable.len(), 2);
    }
}
