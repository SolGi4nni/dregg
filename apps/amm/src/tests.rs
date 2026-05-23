//! Full test suite for the AMM.

use pyana_circuit::field::BabyBear;
use pyana_circuit::stark::{self, StarkAir};
use pyana_dsl_runtime::DslCircuit;

use crate::circuit::{
    self, FEE_BPS, FEE_DENOM, SwapWitness, add_liquidity_circuit, amm_swap_descriptor,
    compute_swap, generate_add_liquidity_trace, generate_swap_trace, swap_circuit,
};
use crate::pool::{LiquidityPool, PoolError};

// =============================================================================
// Pool lifecycle tests
// =============================================================================

#[test]
fn test_create_pool_with_initial_liquidity() {
    let pool = LiquidityPool::create(1, 2, 1000, 4000).unwrap();
    assert_eq!(pool.reserve_a, 1000);
    assert_eq!(pool.reserve_b, 4000);
    assert_eq!(pool.k(), 4_000_000);
    assert!(pool.lp_total_supply > 0);
    // sqrt(1000 * 4000) = sqrt(4_000_000) = 2000
    assert_eq!(pool.lp_total_supply, 2000);
}

#[test]
fn test_create_pool_zero_amount_rejected() {
    assert_eq!(
        LiquidityPool::create(1, 2, 0, 1000).unwrap_err(),
        PoolError::ZeroAmount
    );
    assert_eq!(
        LiquidityPool::create(1, 2, 1000, 0).unwrap_err(),
        PoolError::ZeroAmount
    );
}

// =============================================================================
// Swap tests
// =============================================================================

#[test]
fn test_swap_a_to_b_maintains_invariant() {
    let mut pool = LiquidityPool::create(1, 2, 10_000, 10_000).unwrap();
    let k_before = pool.k();

    let output = pool.swap(100, 1, true).unwrap();

    // k should increase (fee adds to reserves)
    assert!(pool.k() >= k_before);
    // Got some output
    assert!(output.amount_out > 0);
    // Fee was charged
    assert!(output.fee_amount > 0);
    // Reserves updated correctly
    assert_eq!(pool.reserve_a, 10_100); // added 100
    assert_eq!(pool.reserve_b, 10_000 - output.amount_out); // removed output
}

#[test]
fn test_swap_b_to_a_maintains_invariant() {
    let mut pool = LiquidityPool::create(1, 2, 10_000, 10_000).unwrap();
    let k_before = pool.k();

    let output = pool.swap(100, 1, false).unwrap();

    assert!(pool.k() >= k_before);
    assert!(output.amount_out > 0);
    assert_eq!(pool.reserve_b, 10_100);
    assert_eq!(pool.reserve_a, 10_000 - output.amount_out);
}

#[test]
fn test_slippage_violation_rejected() {
    let mut pool = LiquidityPool::create(1, 2, 10_000, 10_000).unwrap();

    // Compute what we'd actually get
    let witness = SwapWitness {
        reserve_a_old: 10_000,
        reserve_b_old: 10_000,
        amount_in: 100,
        min_output: 0,
        direction_a_to_b: true,
    };
    let result = compute_swap(&witness);

    // Set min_output higher than actual output
    let err = pool.swap(100, result.amount_out + 1, true).unwrap_err();
    match err {
        PoolError::SlippageExceeded { expected, minimum } => {
            assert_eq!(expected, result.amount_out);
            assert_eq!(minimum, result.amount_out + 1);
        }
        _ => panic!("expected SlippageExceeded, got {:?}", err),
    }
}

#[test]
fn test_invariant_violation_rejected_adversarial() {
    // This test verifies that the circuit rejects traces with invalid invariant.
    let descriptor = amm_swap_descriptor();
    let circuit = DslCircuit::new(descriptor);

    // Create a trace that VIOLATES the invariant (k_new < k_old)
    let mut row = vec![BabyBear::ZERO; circuit::col::WIDTH];
    row[circuit::col::RESERVE_A_OLD] = BabyBear::new(1000);
    row[circuit::col::RESERVE_B_OLD] = BabyBear::new(1000);
    // Claim new reserves that would decrease k
    row[circuit::col::RESERVE_A_NEW] = BabyBear::new(900);
    row[circuit::col::RESERVE_B_NEW] = BabyBear::new(900);
    // Fake k values
    row[circuit::col::K_OLD] = BabyBear::new(1000) * BabyBear::new(1000);
    // k_new should be 900*900=810000, but K_OLD is 1000000
    row[circuit::col::K_NEW] = BabyBear::new(900) * BabyBear::new(900);
    row[circuit::col::AMOUNT_IN] = BabyBear::new(100);
    row[circuit::col::AMOUNT_OUT] = BabyBear::new(200); // taking too much out
    row[circuit::col::MIN_OUTPUT] = BabyBear::new(1);
    row[circuit::col::DIRECTION] = BabyBear::ONE;

    // Fill fee columns consistently (so those constraints pass)
    let fee_product = BabyBear::new(100) * BabyBear::new(FEE_DENOM - FEE_BPS);
    row[circuit::col::FEE_PRODUCT] = fee_product;
    row[circuit::col::EFFECTIVE_AMOUNT_IN] = BabyBear::new(99); // approximate

    // Slippage columns
    row[circuit::col::SLIPPAGE_DIFF] = BabyBear::new(199);
    // bits for 199: 11000111
    for i in 0..circuit::col::NUM_BITS {
        let bit_col = circuit::col::BITS_START + i;
        row[bit_col] = if (199 >> i) & 1 == 1 {
            BabyBear::ONE
        } else {
            BabyBear::ZERO
        };
    }

    let trace = vec![row.clone(), row];
    let pi = vec![
        BabyBear::new(1000),
        BabyBear::new(1000),
        BabyBear::new(900),
        BabyBear::new(900),
        BabyBear::new(100),
        BabyBear::new(200),
        BabyBear::new(1),
        BabyBear::ONE,
    ];

    // Evaluate constraints manually — at least one should be non-zero
    let alpha = BabyBear::new(7); // arbitrary
    let constraint_val = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);

    // The constraint evaluation should NOT be zero (violation detected)
    assert_ne!(
        constraint_val,
        BabyBear::ZERO,
        "adversarial trace should fail constraints"
    );
}

// =============================================================================
// Liquidity tests
// =============================================================================

#[test]
fn test_add_liquidity_proportional() {
    let mut pool = LiquidityPool::create(1, 2, 1000, 2000).unwrap();
    let supply_before = pool.lp_total_supply;

    // Add 10% more liquidity proportionally
    let output = pool.add_liquidity(100, 200).unwrap();

    assert_eq!(pool.reserve_a, 1100);
    assert_eq!(pool.reserve_b, 2200);
    assert!(output.lp_minted > 0);
    assert_eq!(pool.lp_total_supply, supply_before + output.lp_minted);
}

#[test]
fn test_add_liquidity_disproportional_rejected() {
    let mut pool = LiquidityPool::create(1, 2, 1000, 2000).unwrap();

    // Try non-proportional deposit
    let err = pool.add_liquidity(100, 100).unwrap_err();
    assert_eq!(err, PoolError::DisproportionalDeposit);
}

#[test]
fn test_remove_liquidity_proportional() {
    let mut pool = LiquidityPool::create(1, 2, 1000, 2000).unwrap();
    let total_lp = pool.lp_total_supply;

    // Remove half the liquidity
    let output = pool.remove_liquidity(total_lp / 2).unwrap();

    assert_eq!(output.amount_a, 500);
    assert_eq!(output.amount_b, 1000);
    assert_eq!(pool.reserve_a, 500);
    assert_eq!(pool.reserve_b, 1000);
}

#[test]
fn test_remove_liquidity_insufficient_rejected() {
    let mut pool = LiquidityPool::create(1, 2, 1000, 2000).unwrap();

    let err = pool.remove_liquidity(pool.lp_total_supply + 1).unwrap_err();
    match err {
        PoolError::InsufficientLpTokens { .. } => {}
        _ => panic!("expected InsufficientLpTokens"),
    }
}

// =============================================================================
// Fee accumulation tests
// =============================================================================

#[test]
fn test_fee_accumulation_increases_k() {
    let mut pool = LiquidityPool::create(1, 2, 10_000, 10_000).unwrap();
    let k_initial = pool.k();

    // Execute several swaps
    for _ in 0..10 {
        pool.swap(500, 1, true).unwrap();
        pool.swap(500, 1, false).unwrap();
    }

    // k should have strictly increased due to fees
    assert!(
        pool.k() > k_initial,
        "k should increase from fees: initial={}, final={}",
        k_initial,
        pool.k()
    );
}

// =============================================================================
// Circuit constraint tests
// =============================================================================

#[test]
fn test_swap_circuit_constraints_valid_trace() {
    let circuit = swap_circuit();
    let witness = SwapWitness {
        reserve_a_old: 10_000,
        reserve_b_old: 10_000,
        amount_in: 100,
        min_output: 1,
        direction_a_to_b: true,
    };

    let (trace, pi) = generate_swap_trace(&witness);

    // Verify all constraints evaluate to zero on a valid trace
    let alpha = BabyBear::new(13);
    let val = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
    assert_eq!(
        val,
        BabyBear::ZERO,
        "valid swap trace should satisfy all constraints"
    );
}

#[test]
fn test_swap_circuit_b_to_a() {
    let circuit = swap_circuit();
    let witness = SwapWitness {
        reserve_a_old: 10_000,
        reserve_b_old: 10_000,
        amount_in: 200,
        min_output: 1,
        direction_a_to_b: false,
    };

    let (trace, pi) = generate_swap_trace(&witness);
    let alpha = BabyBear::new(17);
    let val = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
    assert_eq!(
        val,
        BabyBear::ZERO,
        "B->A swap trace should satisfy all constraints"
    );
}

#[test]
fn test_add_liquidity_circuit_valid_trace() {
    let circuit = add_liquidity_circuit();

    let (trace, pi) = generate_add_liquidity_trace(
        1000, // reserve_a_old
        2000, // reserve_b_old
        100,  // amount_a
        200,  // amount_b (proportional: 100/1000 == 200/2000)
        1000, // total_supply_old
        100,  // lp_minted (= 1000 * 100/1000 = 100)
    );

    let alpha = BabyBear::new(19);
    let val = circuit.eval_constraints(&trace[0], &trace[1], &pi, alpha);
    assert_eq!(
        val,
        BabyBear::ZERO,
        "valid add-liquidity trace should satisfy all constraints"
    );
}

// =============================================================================
// STARK prove/verify for swap circuit
// =============================================================================

#[test]
fn test_stark_prove_verify_swap() {
    let circuit = swap_circuit();
    let witness = SwapWitness {
        reserve_a_old: 10_000,
        reserve_b_old: 10_000,
        amount_in: 100,
        min_output: 1,
        direction_a_to_b: true,
    };

    let (trace, pi) = generate_swap_trace(&witness);

    // Generate STARK proof
    let proof = stark::prove(&circuit, &trace, &pi);

    // Verify STARK proof
    let result = stark::verify(&circuit, &proof, &pi);
    assert!(
        result.is_ok(),
        "STARK verification failed: {:?}",
        result.err()
    );
}

#[test]
fn test_stark_prove_verify_swap_b_to_a() {
    let circuit = swap_circuit();
    let witness = SwapWitness {
        reserve_a_old: 5_000,
        reserve_b_old: 20_000,
        amount_in: 500,
        min_output: 1,
        direction_a_to_b: false,
    };

    let (trace, pi) = generate_swap_trace(&witness);

    let proof = stark::prove(&circuit, &trace, &pi);
    let result = stark::verify(&circuit, &proof, &pi);
    assert!(
        result.is_ok(),
        "B->A STARK verification failed: {:?}",
        result.err()
    );
}

#[test]
fn test_stark_rejects_tampered_public_inputs() {
    let circuit = swap_circuit();
    let witness = SwapWitness {
        reserve_a_old: 10_000,
        reserve_b_old: 10_000,
        amount_in: 100,
        min_output: 1,
        direction_a_to_b: true,
    };

    let (trace, pi) = generate_swap_trace(&witness);
    let proof = stark::prove(&circuit, &trace, &pi);

    // Tamper with public inputs (claim different reserves)
    let mut tampered_pi = pi.clone();
    tampered_pi[0] = BabyBear::new(99999); // lie about reserve_a_old

    let result = stark::verify(&circuit, &proof, &tampered_pi);
    assert!(
        result.is_err(),
        "STARK should reject tampered public inputs"
    );
}

// =============================================================================
// Registry tests
// =============================================================================

#[test]
fn test_amm_registry() {
    let mut registry = crate::AmmRegistry::new();

    let pool = LiquidityPool::create(1, 2, 1000, 2000).unwrap();
    let pool_id = pool.id;
    registry.register_pool(pool);

    assert_eq!(registry.pool_count(), 1);
    assert!(registry.get_pool(&pool_id).is_some());
    assert!(registry.find_pool_by_pair(1, 2).is_some());
    assert!(registry.find_pool_by_pair(2, 1).is_some()); // reverse lookup works
    assert!(registry.find_pool_by_pair(1, 3).is_none());
}
