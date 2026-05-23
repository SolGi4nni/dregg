//! Liquidity pool state management.
//!
//! A `LiquidityPool` represents a constant-product AMM pool stored as a HOSTED cell.
//! It maintains reserves for two token types and tracks the LP token supply.

use serde::{Deserialize, Serialize};

use crate::circuit::{FEE_BPS, SwapWitness, compute_swap};
use crate::lp_token::LpTokenId;

/// Unique identifier for a liquidity pool (BLAKE3 hash of creation parameters).
pub type PoolId = [u8; 32];

/// A constant-product AMM liquidity pool.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LiquidityPool {
    /// Pool identity (content-addressed).
    pub id: PoolId,
    /// Asset type for token A.
    pub asset_a: u64,
    /// Asset type for token B.
    pub asset_b: u64,
    /// Current reserve of token A.
    pub reserve_a: u64,
    /// Current reserve of token B.
    pub reserve_b: u64,
    /// Total supply of LP tokens for this pool.
    pub lp_total_supply: u64,
    /// The LP token asset type identifier.
    pub lp_asset_type: u64,
    /// Fee in basis points (default 30 = 0.3%).
    pub fee_bps: u32,
    /// Cumulative k value (for tracking fee accumulation).
    pub cumulative_k: u128,
}

/// Errors from pool operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PoolError {
    /// Insufficient reserves for the requested swap.
    InsufficientLiquidity,
    /// Output amount would be below the minimum (slippage).
    SlippageExceeded { expected: u64, minimum: u64 },
    /// Invalid deposit proportions.
    DisproportionalDeposit,
    /// Pool has zero liquidity.
    EmptyPool,
    /// Amount is zero.
    ZeroAmount,
    /// Insufficient LP tokens for withdrawal.
    InsufficientLpTokens { requested: u64, available: u64 },
    /// Invariant violation detected.
    InvariantViolation { k_old: u128, k_new: u128 },
}

impl std::fmt::Display for PoolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InsufficientLiquidity => write!(f, "insufficient liquidity in pool"),
            Self::SlippageExceeded { expected, minimum } => {
                write!(
                    f,
                    "slippage exceeded: output {expected} < minimum {minimum}"
                )
            }
            Self::DisproportionalDeposit => write!(f, "deposit must be proportional to reserves"),
            Self::EmptyPool => write!(f, "pool has zero liquidity"),
            Self::ZeroAmount => write!(f, "amount must be non-zero"),
            Self::InsufficientLpTokens {
                requested,
                available,
            } => {
                write!(
                    f,
                    "insufficient LP tokens: requested {requested}, available {available}"
                )
            }
            Self::InvariantViolation { k_old, k_new } => {
                write!(f, "invariant violation: k_old={k_old}, k_new={k_new}")
            }
        }
    }
}

impl std::error::Error for PoolError {}

/// Result of a successful swap.
#[derive(Clone, Debug)]
pub struct SwapOutput {
    pub amount_out: u64,
    pub reserve_a_new: u64,
    pub reserve_b_new: u64,
    pub effective_amount_in: u64,
    pub fee_amount: u64,
}

/// Result of adding liquidity.
#[derive(Clone, Debug)]
pub struct AddLiquidityOutput {
    pub lp_minted: u64,
    pub amount_a_used: u64,
    pub amount_b_used: u64,
}

/// Result of removing liquidity.
#[derive(Clone, Debug)]
pub struct RemoveLiquidityOutput {
    pub amount_a: u64,
    pub amount_b: u64,
}

impl LiquidityPool {
    /// Create a new liquidity pool with initial liquidity.
    ///
    /// The initial LP supply equals sqrt(amount_a * amount_b) (geometric mean).
    pub fn create(
        asset_a: u64,
        asset_b: u64,
        initial_a: u64,
        initial_b: u64,
    ) -> Result<Self, PoolError> {
        if initial_a == 0 || initial_b == 0 {
            return Err(PoolError::ZeroAmount);
        }

        // Pool ID = BLAKE3(asset_a || asset_b || initial reserves)
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-amm-pool-v1");
        hasher.update(&asset_a.to_le_bytes());
        hasher.update(&asset_b.to_le_bytes());
        hasher.update(&initial_a.to_le_bytes());
        hasher.update(&initial_b.to_le_bytes());
        let id: PoolId = *hasher.finalize().as_bytes();

        // LP token type = BLAKE3("LP" || pool_id)
        let lp_asset_type = LpTokenId::new(&id).as_asset_type();

        // Initial LP supply = sqrt(initial_a * initial_b) (integer approximation)
        let k = initial_a as u128 * initial_b as u128;
        let lp_supply = isqrt(k) as u64;

        Ok(Self {
            id,
            asset_a,
            asset_b,
            reserve_a: initial_a,
            reserve_b: initial_b,
            lp_total_supply: lp_supply,
            lp_asset_type,
            fee_bps: FEE_BPS,
            cumulative_k: k,
        })
    }

    /// Current invariant k = reserve_a * reserve_b.
    pub fn k(&self) -> u128 {
        self.reserve_a as u128 * self.reserve_b as u128
    }

    /// Execute a swap (A->B or B->A) with slippage protection.
    ///
    /// Returns the swap output on success, updating pool state.
    pub fn swap(
        &mut self,
        amount_in: u64,
        min_output: u64,
        direction_a_to_b: bool,
    ) -> Result<SwapOutput, PoolError> {
        if amount_in == 0 {
            return Err(PoolError::ZeroAmount);
        }

        let witness = SwapWitness {
            reserve_a_old: self.reserve_a,
            reserve_b_old: self.reserve_b,
            amount_in,
            min_output,
            direction_a_to_b,
        };

        let result = compute_swap(&witness);

        // Verify slippage
        if result.amount_out < min_output {
            return Err(PoolError::SlippageExceeded {
                expected: result.amount_out,
                minimum: min_output,
            });
        }

        // Verify output is feasible
        let reserve_out = if direction_a_to_b {
            self.reserve_b
        } else {
            self.reserve_a
        };
        if result.amount_out >= reserve_out {
            return Err(PoolError::InsufficientLiquidity);
        }

        // Verify invariant
        let k_old = self.k();
        let k_new = result.reserve_a_new as u128 * result.reserve_b_new as u128;
        if k_new < k_old {
            return Err(PoolError::InvariantViolation { k_old, k_new });
        }

        let fee_amount = amount_in - result.effective_amount_in;

        // Apply state update
        self.reserve_a = result.reserve_a_new;
        self.reserve_b = result.reserve_b_new;
        self.cumulative_k = k_new;

        Ok(SwapOutput {
            amount_out: result.amount_out,
            reserve_a_new: self.reserve_a,
            reserve_b_new: self.reserve_b,
            effective_amount_in: result.effective_amount_in,
            fee_amount,
        })
    }

    /// Add liquidity proportionally to the current reserves.
    ///
    /// For the first deposit (empty pool), any ratio is accepted.
    /// For subsequent deposits, amounts must be proportional.
    pub fn add_liquidity(
        &mut self,
        amount_a: u64,
        amount_b: u64,
    ) -> Result<AddLiquidityOutput, PoolError> {
        if amount_a == 0 || amount_b == 0 {
            return Err(PoolError::ZeroAmount);
        }

        // Check proportionality: amount_a / reserve_a == amount_b / reserve_b
        // Cross-multiply: amount_a * reserve_b == amount_b * reserve_a
        if self.reserve_a > 0 && self.reserve_b > 0 {
            let cross_a = amount_a as u128 * self.reserve_b as u128;
            let cross_b = amount_b as u128 * self.reserve_a as u128;
            if cross_a != cross_b {
                return Err(PoolError::DisproportionalDeposit);
            }
        }

        // Mint LP tokens proportional to the deposit
        let lp_minted = if self.lp_total_supply == 0 {
            // First deposit
            isqrt(amount_a as u128 * amount_b as u128) as u64
        } else {
            // lp_minted = total_supply * amount_a / reserve_a
            (self.lp_total_supply as u128 * amount_a as u128 / self.reserve_a as u128) as u64
        };

        self.reserve_a += amount_a;
        self.reserve_b += amount_b;
        self.lp_total_supply += lp_minted;
        self.cumulative_k = self.k();

        Ok(AddLiquidityOutput {
            lp_minted,
            amount_a_used: amount_a,
            amount_b_used: amount_b,
        })
    }

    /// Remove liquidity by burning LP tokens. Returns proportional share of reserves.
    pub fn remove_liquidity(&mut self, lp_amount: u64) -> Result<RemoveLiquidityOutput, PoolError> {
        if lp_amount == 0 {
            return Err(PoolError::ZeroAmount);
        }
        if lp_amount > self.lp_total_supply {
            return Err(PoolError::InsufficientLpTokens {
                requested: lp_amount,
                available: self.lp_total_supply,
            });
        }

        // Proportional share: amount = reserves * lp_amount / total_supply
        let amount_a =
            (self.reserve_a as u128 * lp_amount as u128 / self.lp_total_supply as u128) as u64;
        let amount_b =
            (self.reserve_b as u128 * lp_amount as u128 / self.lp_total_supply as u128) as u64;

        self.reserve_a -= amount_a;
        self.reserve_b -= amount_b;
        self.lp_total_supply -= lp_amount;
        self.cumulative_k = self.k();

        Ok(RemoveLiquidityOutput { amount_a, amount_b })
    }

    /// Get the spot price of A in terms of B (reserve_b / reserve_a).
    pub fn price_a_in_b(&self) -> f64 {
        if self.reserve_a == 0 {
            return 0.0;
        }
        self.reserve_b as f64 / self.reserve_a as f64
    }

    /// Get the spot price of B in terms of A (reserve_a / reserve_b).
    pub fn price_b_in_a(&self) -> f64 {
        if self.reserve_b == 0 {
            return 0.0;
        }
        self.reserve_a as f64 / self.reserve_b as f64
    }
}

/// Integer square root (floor).
fn isqrt(n: u128) -> u128 {
    if n == 0 {
        return 0;
    }
    let mut x = n;
    let mut y = (x + 1) / 2;
    while y < x {
        x = y;
        y = (x + n / x) / 2;
    }
    x
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_isqrt() {
        assert_eq!(isqrt(0), 0);
        assert_eq!(isqrt(1), 1);
        assert_eq!(isqrt(4), 2);
        assert_eq!(isqrt(9), 3);
        assert_eq!(isqrt(10), 3);
        assert_eq!(isqrt(1_000_000), 1000);
    }

    #[test]
    fn test_create_pool() {
        let pool = LiquidityPool::create(1, 2, 1000, 2000).unwrap();
        assert_eq!(pool.reserve_a, 1000);
        assert_eq!(pool.reserve_b, 2000);
        assert_eq!(pool.k(), 2_000_000);
    }
}
