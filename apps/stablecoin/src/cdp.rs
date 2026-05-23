//! Collateralized Debt Position (CDP) lifecycle management.
//!
//! A CDP allows a user to lock collateral and mint stablecoins against it.
//! The position must maintain the required collateral ratio at all times.
//!
//! # Lifecycle
//!
//! 1. **Open**: Deposit collateral, creating a new position.
//! 2. **Mint**: Issue stablecoins (increases debt), proving ratio is maintained.
//! 3. **Repay**: Burn stablecoins (decreases debt), releasing collateral capacity.
//! 4. **Close**: Repay all debt, withdraw all collateral.
//! 5. **Liquidate**: External trigger when ratio drops below threshold.
//!
//! Each state-modifying action requires a STARK proof that the resulting position
//! satisfies the collateral ratio constraint.

use pyana_cell::{CellId, Note};
use pyana_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

use crate::circuit::{self, BPS_SCALE, CdpWitness};
use crate::oracle::{OracleError, PriceAttestation};

/// Asset type identifier for the stablecoin (PUSD — Pyana USD).
pub const PUSD_ASSET_TYPE: u64 = 0x_5055_5344; // "PUSD" in ASCII

/// Asset type identifier for ETH collateral.
pub const ETH_ASSET_TYPE: u64 = 0x_4554_4800; // "ETH\0" in ASCII

/// A collateralized debt position.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CollateralPosition {
    /// Unique position identifier (BLAKE3 hash of creation parameters).
    pub id: [u8; 32],
    /// The owner's cell identity.
    pub owner: CellId,
    /// Amount of collateral locked (in smallest unit of collateral asset).
    pub collateral_amount: u64,
    /// Asset type of the collateral.
    pub collateral_asset: u64,
    /// Outstanding stablecoin debt (in PUSD smallest unit).
    pub debt_amount: u64,
    /// Minimum collateral ratio in basis points (e.g., 15000 = 150%).
    pub ratio_bps: u64,
    /// Block height at which this position was opened.
    pub opened_at: u64,
    /// Current status of the position.
    pub status: PositionStatus,
    /// The latest oracle commitment used to prove this position's health.
    pub last_oracle_commitment: Option<BabyBear>,
}

/// Status of a CDP position.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PositionStatus {
    /// Active and healthy.
    Active,
    /// Closed by owner (all debt repaid, collateral withdrawn).
    Closed,
    /// Liquidated due to under-collateralization.
    Liquidated {
        /// Block height at which liquidation occurred.
        liquidated_at: u64,
        /// The liquidator's cell ID.
        liquidator: CellId,
    },
}

/// Errors from CDP operations.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum CdpError {
    #[error("position {id:?} is not active")]
    NotActive { id: [u8; 32] },
    #[error("insufficient collateral: need {required}, have {available}")]
    InsufficientCollateral { required: u64, available: u64 },
    #[error("repayment {amount} exceeds outstanding debt {debt}")]
    ExcessiveRepayment { amount: u64, debt: u64 },
    #[error("position is still healthy (ratio {actual_bps} >= {required_bps})")]
    StillHealthy { actual_bps: u64, required_bps: u64 },
    #[error("proof generation failed: {reason}")]
    ProofFailed { reason: String },
    #[error("oracle error: {0}")]
    Oracle(String),
    #[error("unauthorized: caller {caller:?} is not the owner {owner:?}")]
    Unauthorized { caller: CellId, owner: CellId },
    #[error("zero amount not allowed")]
    ZeroAmount,
}

impl From<OracleError> for CdpError {
    fn from(e: OracleError) -> Self {
        CdpError::Oracle(e.to_string())
    }
}

/// Result of a CDP operation that modifies state.
#[derive(Clone, Debug)]
pub struct CdpTransition {
    /// Updated position state after the transition.
    pub position: CollateralPosition,
    /// STARK proof of the collateral ratio constraint.
    pub proof: Vec<u8>,
    /// Notes created (minted stablecoins or change outputs).
    pub created_notes: Vec<Note>,
    /// Notes consumed (burned stablecoins).
    pub consumed_notes: Vec<Note>,
}

impl CollateralPosition {
    /// Open a new CDP position by depositing collateral.
    pub fn open(
        owner: CellId,
        collateral_amount: u64,
        collateral_asset: u64,
        ratio_bps: u64,
        current_height: u64,
    ) -> Result<Self, CdpError> {
        if collateral_amount == 0 {
            return Err(CdpError::ZeroAmount);
        }

        // Compute position ID
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-cdp-position-v1");
        hasher.update(&owner.0);
        hasher.update(&collateral_amount.to_le_bytes());
        hasher.update(&current_height.to_le_bytes());
        let id = *hasher.finalize().as_bytes();

        Ok(CollateralPosition {
            id,
            owner,
            collateral_amount,
            collateral_asset,
            debt_amount: 0,
            ratio_bps,
            opened_at: current_height,
            status: PositionStatus::Active,
            last_oracle_commitment: None,
        })
    }

    /// Mint stablecoins against this position's collateral.
    ///
    /// Requires a price attestation to prove the resulting position is healthy.
    /// Returns a transition containing the proof and minted note.
    pub fn mint(
        &mut self,
        mint_amount: u64,
        price_attestation: &PriceAttestation,
        _current_time: u64,
        max_age: u64,
    ) -> Result<CdpTransition, CdpError> {
        if self.status != PositionStatus::Active {
            return Err(CdpError::NotActive { id: self.id });
        }
        if mint_amount == 0 {
            return Err(CdpError::ZeroAmount);
        }

        let new_debt = self.debt_amount + mint_amount;

        // Build witness and check health
        let witness = CdpWitness {
            collateral_amount: self.collateral_amount,
            price: price_attestation.price,
            debt_amount: new_debt,
            ratio_bps: self.ratio_bps,
            position_id: self.id,
            oracle_commitment: price_attestation.commitment(),
            price_timestamp: price_attestation.timestamp,
            max_age,
        };

        if !witness.is_healthy() {
            let collateral_value = self.collateral_amount * price_attestation.price * BPS_SCALE;
            let required = new_debt * self.ratio_bps;
            return Err(CdpError::InsufficientCollateral {
                required,
                available: collateral_value,
            });
        }

        // Generate proof
        let proof =
            circuit::prove_cdp_ratio(&witness).map_err(|e| CdpError::ProofFailed { reason: e })?;

        // Update state
        self.debt_amount = new_debt;
        self.last_oracle_commitment = Some(price_attestation.commitment());

        // Create a stablecoin note
        let mut note_randomness = [0u8; 32];
        // Deterministic randomness for testing (in production, use getrandom)
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"mint-randomness");
        hasher.update(&self.id);
        hasher.update(&mint_amount.to_le_bytes());
        hasher.update(&self.debt_amount.to_le_bytes());
        note_randomness.copy_from_slice(hasher.finalize().as_bytes());

        let mut creation_nonce = [0u8; 32];
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"mint-nonce");
        hasher.update(&self.id);
        hasher.update(&new_debt.to_le_bytes());
        creation_nonce.copy_from_slice(hasher.finalize().as_bytes());

        let minted_note = Note {
            owner: self.owner.0,
            fields: [PUSD_ASSET_TYPE, mint_amount, 0, 0, 0, 0, 0, 0],
            randomness: note_randomness,
            creation_nonce,
        };

        Ok(CdpTransition {
            position: self.clone(),
            proof,
            created_notes: vec![minted_note],
            consumed_notes: vec![],
        })
    }

    /// Repay stablecoins to reduce debt.
    ///
    /// Burns the repayment notes and reduces the outstanding debt.
    pub fn repay(
        &mut self,
        repay_amount: u64,
        price_attestation: &PriceAttestation,
        max_age: u64,
    ) -> Result<CdpTransition, CdpError> {
        if self.status != PositionStatus::Active {
            return Err(CdpError::NotActive { id: self.id });
        }
        if repay_amount == 0 {
            return Err(CdpError::ZeroAmount);
        }
        if repay_amount > self.debt_amount {
            return Err(CdpError::ExcessiveRepayment {
                amount: repay_amount,
                debt: self.debt_amount,
            });
        }

        let new_debt = self.debt_amount - repay_amount;

        // If new_debt > 0, prove the position is still healthy.
        // If new_debt == 0, the position can be closed without ratio proof.
        let proof = if new_debt > 0 {
            let witness = CdpWitness {
                collateral_amount: self.collateral_amount,
                price: price_attestation.price,
                debt_amount: new_debt,
                ratio_bps: self.ratio_bps,
                position_id: self.id,
                oracle_commitment: price_attestation.commitment(),
                price_timestamp: price_attestation.timestamp,
                max_age,
            };
            circuit::prove_cdp_ratio(&witness).map_err(|e| CdpError::ProofFailed { reason: e })?
        } else {
            // No proof needed: zero debt means infinite ratio
            Vec::new()
        };

        // Update state
        self.debt_amount = new_debt;
        self.last_oracle_commitment = Some(price_attestation.commitment());

        // Create burn note (note being consumed)
        let mut creation_nonce = [0u8; 32];
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"repay-nonce");
        hasher.update(&self.id);
        hasher.update(&repay_amount.to_le_bytes());
        creation_nonce.copy_from_slice(hasher.finalize().as_bytes());

        let burned_note = Note {
            owner: self.owner.0,
            fields: [PUSD_ASSET_TYPE, repay_amount, 0, 0, 0, 0, 0, 0],
            randomness: [0u8; 32],
            creation_nonce,
        };

        Ok(CdpTransition {
            position: self.clone(),
            proof,
            created_notes: vec![],
            consumed_notes: vec![burned_note],
        })
    }

    /// Close the position entirely (requires zero debt).
    pub fn close(&mut self) -> Result<CdpTransition, CdpError> {
        if self.status != PositionStatus::Active {
            return Err(CdpError::NotActive { id: self.id });
        }
        if self.debt_amount > 0 {
            return Err(CdpError::ExcessiveRepayment {
                amount: 0,
                debt: self.debt_amount,
            });
        }

        self.status = PositionStatus::Closed;

        Ok(CdpTransition {
            position: self.clone(),
            proof: Vec::new(), // No ratio proof needed for close
            created_notes: vec![],
            consumed_notes: vec![],
        })
    }

    /// Compute the current collateral ratio in basis points.
    ///
    /// Returns `None` if debt is zero (infinite ratio).
    pub fn collateral_ratio_bps(&self, price: u64) -> Option<u64> {
        if self.debt_amount == 0 {
            return None; // Infinite ratio
        }
        let collateral_value = self.collateral_amount as u128 * price as u128;
        let ratio = (collateral_value * BPS_SCALE as u128) / self.debt_amount as u128;
        Some(ratio as u64)
    }

    /// Check if the position is under-collateralized at the given price.
    pub fn is_liquidatable(&self, price: u64) -> bool {
        if self.status != PositionStatus::Active || self.debt_amount == 0 {
            return false;
        }
        match self.collateral_ratio_bps(price) {
            Some(ratio) => ratio < self.ratio_bps,
            None => false,
        }
    }
}

/// The stablecoin registry: tracks all active positions.
#[derive(Clone, Debug, Default)]
pub struct StablecoinRegistry {
    /// All positions indexed by ID.
    positions: Vec<CollateralPosition>,
    /// Total stablecoins in circulation.
    pub total_supply: u64,
}

impl StablecoinRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a newly opened position.
    pub fn register(&mut self, position: CollateralPosition) {
        self.positions.push(position);
    }

    /// Update a position after a state transition.
    pub fn update(&mut self, position: &CollateralPosition) {
        if let Some(p) = self.positions.iter_mut().find(|p| p.id == position.id) {
            *p = position.clone();
        }
    }

    /// Get a position by ID.
    pub fn get(&self, id: &[u8; 32]) -> Option<&CollateralPosition> {
        self.positions.iter().find(|p| p.id == *id)
    }

    /// Get a mutable reference to a position by ID.
    pub fn get_mut(&mut self, id: &[u8; 32]) -> Option<&mut CollateralPosition> {
        self.positions.iter_mut().find(|p| p.id == *id)
    }

    /// Get all active positions.
    pub fn active_positions(&self) -> Vec<&CollateralPosition> {
        self.positions
            .iter()
            .filter(|p| p.status == PositionStatus::Active)
            .collect()
    }

    /// Get all liquidatable positions at the given price.
    pub fn liquidatable_positions(&self, asset: u64, price: u64) -> Vec<&CollateralPosition> {
        self.positions
            .iter()
            .filter(|p| p.collateral_asset == asset && p.is_liquidatable(price))
            .collect()
    }

    /// Record minting (increases total supply).
    pub fn record_mint(&mut self, amount: u64) {
        self.total_supply += amount;
    }

    /// Record burning (decreases total supply).
    pub fn record_burn(&mut self, amount: u64) {
        self.total_supply = self.total_supply.saturating_sub(amount);
    }

    /// Total value locked across all active positions (at given price).
    pub fn total_value_locked(&self, asset: u64, price: u64) -> u128 {
        self.positions
            .iter()
            .filter(|p| p.collateral_asset == asset && p.status == PositionStatus::Active)
            .map(|p| p.collateral_amount as u128 * price as u128)
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::MIN_RATIO_BPS;

    fn test_owner() -> CellId {
        CellId([0xAA; 32])
    }

    fn test_attestation(price: u64, timestamp: u64) -> PriceAttestation {
        crate::oracle::test_attestation("ETH/USD", price, timestamp, [0x01; 32])
    }

    #[test]
    fn open_position() {
        let position =
            CollateralPosition::open(test_owner(), 1000, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
                .unwrap();

        assert_eq!(position.collateral_amount, 1000);
        assert_eq!(position.debt_amount, 0);
        assert_eq!(position.status, PositionStatus::Active);
    }

    #[test]
    fn open_zero_collateral_fails() {
        let result = CollateralPosition::open(test_owner(), 0, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100);
        assert!(matches!(result, Err(CdpError::ZeroAmount)));
    }

    #[test]
    fn mint_stablecoins() {
        let mut position =
            CollateralPosition::open(test_owner(), 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
                .unwrap();

        let attestation = test_attestation(2000, 90);
        // collateral_value = 100 * 2000 = 200_000
        // max mintable at 150%: 200_000 * 10000 / 15000 = 133_333
        let transition = position.mint(100_000, &attestation, 95, 50).unwrap();

        assert_eq!(position.debt_amount, 100_000);
        assert!(!transition.proof.is_empty());
        assert_eq!(transition.created_notes.len(), 1);
        assert_eq!(transition.created_notes[0].fields[0], PUSD_ASSET_TYPE);
        assert_eq!(transition.created_notes[0].fields[1], 100_000);
    }

    #[test]
    fn mint_exceeding_ratio_fails() {
        let mut position =
            CollateralPosition::open(test_owner(), 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
                .unwrap();

        let attestation = test_attestation(2000, 90);
        // collateral_value = 100 * 2000 = 200_000
        // Trying to mint 200_000 (would need 200_000 * 15000 / 10000 = 300_000 collateral value)
        let result = position.mint(200_000, &attestation, 95, 50);
        assert!(matches!(
            result,
            Err(CdpError::InsufficientCollateral { .. })
        ));
    }

    #[test]
    fn repay_debt() {
        let mut position =
            CollateralPosition::open(test_owner(), 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
                .unwrap();

        let attestation = test_attestation(2000, 90);
        position.mint(50_000, &attestation, 95, 50).unwrap();
        assert_eq!(position.debt_amount, 50_000);

        let transition = position.repay(30_000, &attestation, 50).unwrap();
        assert_eq!(position.debt_amount, 20_000);
        assert!(!transition.proof.is_empty()); // Still has debt, needs ratio proof
        assert_eq!(transition.consumed_notes.len(), 1);
    }

    #[test]
    fn repay_all_and_close() {
        let mut position =
            CollateralPosition::open(test_owner(), 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
                .unwrap();

        let attestation = test_attestation(2000, 90);
        position.mint(50_000, &attestation, 95, 50).unwrap();
        position.repay(50_000, &attestation, 50).unwrap();
        assert_eq!(position.debt_amount, 0);

        let transition = position.close().unwrap();
        assert_eq!(transition.position.status, PositionStatus::Closed);
    }

    #[test]
    fn collateral_ratio_calculation() {
        let mut position =
            CollateralPosition::open(test_owner(), 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
                .unwrap();
        position.debt_amount = 100_000;

        // collateral_value = 100 * 2000 = 200_000
        // ratio = 200_000 * 10000 / 100_000 = 20_000 bps = 200%
        assert_eq!(position.collateral_ratio_bps(2000), Some(20_000));

        // At price 1000: ratio = 100_000 * 10000 / 100_000 = 10_000 bps = 100%
        assert_eq!(position.collateral_ratio_bps(1000), Some(10_000));
        assert!(position.is_liquidatable(1000)); // 100% < 150%
    }

    #[test]
    fn zero_debt_infinite_ratio() {
        let position =
            CollateralPosition::open(test_owner(), 100, ETH_ASSET_TYPE, MIN_RATIO_BPS, 100)
                .unwrap();
        assert_eq!(position.collateral_ratio_bps(2000), None);
        assert!(!position.is_liquidatable(2000));
    }
}
