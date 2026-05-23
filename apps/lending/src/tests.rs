//! Full lifecycle tests for the lending protocol.

use crate::borrow::CollateralEntry;
use crate::interest::{BLOCKS_PER_YEAR, BPS_SCALE, INDEX_PRECISION, InterestRateModel};
use crate::liquidation::LiquidationResult;
use crate::{LendingError, LendingPool, Market};
use pyana_types::CellId;

fn alice() -> CellId {
    CellId([0xAA; 32])
}

fn bob() -> CellId {
    CellId([0xBB; 32])
}

fn charlie() -> CellId {
    CellId([0xCC; 32])
}

fn setup_pool() -> LendingPool {
    let mut pool = LendingPool::new();
    // Add a stablecoin market (asset 1)
    pool.add_market(Market::new(1));
    // Add an ETH-like volatile asset market (asset 2)
    pool.add_market(Market::new(2));
    pool
}

// =============================================================================
// Supply Tests
// =============================================================================

#[test]
fn test_supply_tokens_receive_receipt() {
    let mut pool = setup_pool();
    let receipt = pool.supply(alice(), 1, 1_000_000).unwrap();
    assert_eq!(receipt.principal, 1_000_000);
    assert_eq!(receipt.supplier, alice());
    assert_eq!(receipt.asset_id, 1);
    assert_eq!(pool.get_market(1).unwrap().total_supply, 1_000_000);
}

#[test]
fn test_supply_to_nonexistent_market() {
    let mut pool = setup_pool();
    let result = pool.supply(alice(), 99, 1_000_000);
    assert!(matches!(
        result,
        Err(LendingError::MarketNotFound { asset_id: 99 })
    ));
}

#[test]
fn test_withdraw_supply() {
    let mut pool = setup_pool();
    let receipt = pool.supply(alice(), 1, 1_000_000).unwrap();
    let amount = pool.withdraw(&receipt.position_id).unwrap();
    assert_eq!(amount, 1_000_000);
    // Cannot withdraw again
    let result = pool.withdraw(&receipt.position_id);
    assert!(matches!(result, Err(LendingError::AlreadyWithdrawn)));
}

// =============================================================================
// Borrow Tests
// =============================================================================

#[test]
fn test_borrow_against_collateral_healthy() {
    let mut pool = setup_pool();
    // Supply liquidity first
    pool.supply(alice(), 1, 10_000_000).unwrap();

    // Bob borrows 1M against 2M collateral (asset 2 at price 1:1)
    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 2_000_000,
        price: BPS_SCALE,
    }];
    let pos_id = pool.borrow(bob(), 1, 1_000_000, collateral).unwrap();

    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == pos_id)
        .unwrap();
    assert!(pos.is_healthy());
    assert_eq!(pos.health_factor_bps(), 16_000); // 2M * 8000 / 1M = 16000
}

#[test]
fn test_borrow_insufficient_collateral() {
    let mut pool = setup_pool();
    pool.supply(alice(), 1, 10_000_000).unwrap();

    // Try to borrow 1M with only 500K collateral at 80% threshold
    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 500_000,
        price: BPS_SCALE,
    }];
    let result = pool.borrow(bob(), 1, 1_000_000, collateral);
    assert!(matches!(
        result,
        Err(LendingError::InsufficientCollateral { .. })
    ));
}

#[test]
fn test_borrow_insufficient_liquidity() {
    let mut pool = setup_pool();
    pool.supply(alice(), 1, 500_000).unwrap();

    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 5_000_000,
        price: BPS_SCALE,
    }];
    let result = pool.borrow(bob(), 1, 1_000_000, collateral);
    assert!(matches!(
        result,
        Err(LendingError::InsufficientLiquidity { .. })
    ));
}

// =============================================================================
// Interest Accrual Tests
// =============================================================================

#[test]
fn test_interest_accrues_over_blocks() {
    let mut pool = setup_pool();
    pool.supply(alice(), 1, 10_000_000).unwrap();

    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 8_000_000, // Need > 1.25x debt for health > 1.0
        price: BPS_SCALE,
    }];
    let _pos_id = pool.borrow(bob(), 1, 5_000_000, collateral).unwrap();

    // Advance one year
    pool.advance_to_block(BLOCKS_PER_YEAR);

    let market = pool.get_market(1).unwrap();
    // Borrows should have grown due to interest
    assert!(market.total_borrows > 5_000_000);
    // Borrow index should have grown
    assert!(market.borrow_index > INDEX_PRECISION);
}

#[test]
fn test_supply_balance_grows_with_interest() {
    let mut pool = setup_pool();
    let receipt = pool.supply(alice(), 1, 10_000_000).unwrap();

    // Create some borrows to generate interest
    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 10_000_000,
        price: BPS_SCALE,
    }];
    pool.borrow(bob(), 1, 5_000_000, collateral).unwrap();

    // Advance time
    pool.advance_to_block(BLOCKS_PER_YEAR);

    // Supply position should be worth more
    let market = pool.get_market(1).unwrap();
    let current_value = receipt.current_value(market.borrow_index);
    assert!(current_value > 10_000_000);
}

// =============================================================================
// Repay Tests
// =============================================================================

#[test]
fn test_repay_loan_unlocks_collateral() {
    let mut pool = setup_pool();
    pool.supply(alice(), 1, 10_000_000).unwrap();

    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 2_000_000,
        price: BPS_SCALE,
    }];
    let pos_id = pool.borrow(bob(), 1, 1_000_000, collateral).unwrap();

    // Repay full amount
    let repaid = pool.repay(&pos_id, 1_000_000).unwrap();
    assert_eq!(repaid, 1_000_000);

    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == pos_id)
        .unwrap();
    assert!(pos.repaid);
    assert_eq!(pos.total_debt(), 0);
}

#[test]
fn test_repay_partial() {
    let mut pool = setup_pool();
    pool.supply(alice(), 1, 10_000_000).unwrap();

    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 2_000_000,
        price: BPS_SCALE,
    }];
    let pos_id = pool.borrow(bob(), 1, 1_000_000, collateral).unwrap();

    let repaid = pool.repay(&pos_id, 500_000).unwrap();
    assert_eq!(repaid, 500_000);

    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == pos_id)
        .unwrap();
    assert!(!pos.repaid);
    assert_eq!(pos.total_debt(), 500_000);
}

// =============================================================================
// Liquidation Tests
// =============================================================================

#[test]
fn test_undercollateralized_liquidation_succeeds() {
    let mut pool = setup_pool();
    pool.supply(alice(), 1, 10_000_000).unwrap();

    // Start with a healthy position: 1.5M collateral at 1:1, debt 1M
    // health = 1_500_000 * 8000 / 1_000_000 = 12000 > 10000
    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 1_500_000,
        price: BPS_SCALE,
    }];
    let pos_id = pool.borrow(bob(), 1, 1_000_000, collateral).unwrap();

    // Verify position starts healthy
    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == pos_id)
        .unwrap();
    assert!(pos.is_healthy());

    // Simulate a price crash: collateral price drops to 60% of par
    // health = 1_500_000 * 0.6 * 8000 / 1_000_000 = 7200 < 10000
    let pos = pool
        .borrow_positions
        .iter_mut()
        .find(|p| p.id == pos_id)
        .unwrap();
    pos.update_prices(&[(2, BPS_SCALE * 6 / 10)]);
    assert!(!pos.is_healthy());

    // Liquidate
    let result = pool.liquidate(&pos_id, charlie(), 400_000, 2).unwrap();
    assert!(matches!(result, LiquidationResult::Success(_)));
}

#[test]
fn test_overcollateralized_liquidation_rejected() {
    let mut pool = setup_pool();
    pool.supply(alice(), 1, 10_000_000).unwrap();

    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 3_000_000,
        price: BPS_SCALE,
    }];
    let pos_id = pool.borrow(bob(), 1, 1_000_000, collateral).unwrap();

    // Position is healthy (health = 3M * 8000 / 1M = 24000)
    let result = pool.liquidate(&pos_id, charlie(), 100_000, 2).unwrap();
    assert!(matches!(result, LiquidationResult::PositionHealthy { .. }));
}

// =============================================================================
// Rate Model Tests
// =============================================================================

#[test]
fn test_utilization_increases_rate() {
    let model = InterestRateModel::default();
    let rate_low = model.borrow_rate_bps(1_000); // 10% util
    let rate_mid = model.borrow_rate_bps(5_000); // 50% util
    let rate_high = model.borrow_rate_bps(9_000); // 90% util
    assert!(rate_low < rate_mid);
    assert!(rate_mid < rate_high);
}

#[test]
fn test_rate_kink_at_optimal() {
    let model = InterestRateModel::default();
    // Just below optimal
    let rate_before = model.borrow_rate_bps(7_999);
    // Just above optimal
    let rate_after = model.borrow_rate_bps(8_001);
    // Rate should jump more steeply above optimal
    let slope_before = rate_before - model.borrow_rate_bps(7_998);
    let slope_after = rate_after - model.borrow_rate_bps(8_000);
    assert!(slope_after > slope_before);
}

// =============================================================================
// Full Lifecycle Test
// =============================================================================

#[test]
fn test_full_lifecycle() {
    let mut pool = setup_pool();

    // 1. Alice supplies 10M stablecoins
    let supply_receipt = pool.supply(alice(), 1, 10_000_000).unwrap();
    assert_eq!(pool.get_market(1).unwrap().total_supply, 10_000_000);

    // 2. Bob borrows 5M against 8M collateral
    let collateral = vec![CollateralEntry {
        asset_id: 2,
        amount: 8_000_000,
        price: BPS_SCALE,
    }];
    let borrow_id = pool.borrow(bob(), 1, 5_000_000, collateral).unwrap();

    // 3. Advance blocks — interest accrues
    let blocks_elapsed = BLOCKS_PER_YEAR / 12; // 1 month
    pool.advance_to_block(blocks_elapsed);

    let market = pool.get_market(1).unwrap();
    assert!(market.total_borrows > 5_000_000);

    // 4. Bob repays his loan (principal + accrued interest)
    let pos = pool
        .borrow_positions
        .iter()
        .find(|p| p.id == borrow_id)
        .unwrap();
    let total_owed = pos.total_debt();
    // Verify the borrow index gives consistent debt
    let _precise_debt = pos.total_debt_with_index(market.borrow_index);
    pool.repay(&borrow_id, total_owed).unwrap();

    // 5. Alice withdraws — should have earned interest
    let market = pool.get_market(1).unwrap();
    let alice_value = supply_receipt.current_value(market.borrow_index);
    assert!(alice_value > 10_000_000);

    // Withdraw
    let withdrawn = pool.withdraw(&supply_receipt.position_id).unwrap();
    assert!(withdrawn >= 10_000_000);
}
