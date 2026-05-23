//! Demo: create a pool, add liquidity, and execute swaps.
//!
//! Run with: `cargo run -p pyana-amm --example swap_demo`

use pyana_amm::AmmRegistry;
use pyana_amm::circuit::{SwapWitness, generate_swap_trace, swap_circuit};
use pyana_amm::lp_token::{LpTokenId, lp_amount, lp_note_commitment, mint_lp_note};
use pyana_amm::pool::LiquidityPool;
use pyana_amm::router::{execute_route, find_route};
use pyana_circuit::stark;

fn main() {
    println!("=== Pyana AMM Demo ===\n");

    // 1. Create a pool with initial liquidity
    println!("--- Step 1: Create Pool ---");
    let mut pool = LiquidityPool::create(
        1, // asset A (e.g., PYANA)
        2, // asset B (e.g., USDC)
        10_000, 50_000,
    )
    .unwrap();
    println!(
        "Pool created: A={}, B={}, k={}, LP supply={}",
        pool.reserve_a,
        pool.reserve_b,
        pool.k(),
        pool.lp_total_supply,
    );
    println!("Price of A in B: {:.4}", pool.price_a_in_b());
    println!();

    // 2. Execute a swap A->B
    println!("--- Step 2: Swap 500 A -> B ---");
    let output = pool.swap(500, 1, true).unwrap();
    println!(
        "Swapped 500 A -> {} B (fee: {} A)",
        output.amount_out, output.fee_amount
    );
    println!(
        "New reserves: A={}, B={}, k={}",
        pool.reserve_a,
        pool.reserve_b,
        pool.k()
    );
    println!("New price of A in B: {:.4}", pool.price_a_in_b());
    println!();

    // 3. Execute a swap B->A
    println!("--- Step 3: Swap 1000 B -> A ---");
    let output = pool.swap(1000, 1, false).unwrap();
    println!(
        "Swapped 1000 B -> {} A (fee: {} B)",
        output.amount_out, output.fee_amount
    );
    println!(
        "New reserves: A={}, B={}, k={}",
        pool.reserve_a,
        pool.reserve_b,
        pool.k()
    );
    println!();

    // 4. Add liquidity
    println!("--- Step 4: Add Liquidity ---");
    // Calculate proportional amounts. We need exact cross-multiplication:
    // add_a * reserve_b == add_b * reserve_a
    // Use GCD to find exact proportional amounts.
    let g = gcd(pool.reserve_a, pool.reserve_b);
    let ratio_a = pool.reserve_a / g;
    let ratio_b = pool.reserve_b / g;
    // Deposit a multiple of the simplified ratio
    let multiplier = 10u64;
    let add_a = ratio_a * multiplier;
    let add_b = ratio_b * multiplier;
    let liq_output = pool.add_liquidity(add_a, add_b).unwrap();
    println!(
        "Added {}/{} liquidity, minted {} LP tokens",
        add_a, add_b, liq_output.lp_minted
    );
    println!("Total LP supply: {}", pool.lp_total_supply);
    println!();

    // 5. Mint LP token as a note
    println!("--- Step 5: LP Token Note ---");
    let lp_id = LpTokenId::new(&pool.id);
    let owner = [1u8; 32];
    let nonce = [42u8; 32];
    let lp_note = mint_lp_note(owner, &lp_id, liq_output.lp_minted, nonce);
    let commitment = lp_note_commitment(&lp_note);
    println!(
        "Minted LP note: amount={}, commitment={:?}",
        lp_amount(&lp_note),
        &commitment.0[..8]
    );
    println!();

    // 6. Generate and verify STARK proof for the swap
    println!("--- Step 6: STARK Proof ---");
    let circuit = swap_circuit();
    let witness = SwapWitness {
        reserve_a_old: 10_000,
        reserve_b_old: 50_000,
        amount_in: 500,
        min_output: 1,
        direction_a_to_b: true,
    };
    let (trace, pi) = generate_swap_trace(&witness);
    let proof = stark::prove(&circuit, &trace, &pi);
    println!("Proof generated: {} bytes", std::mem::size_of_val(&proof));
    let verify_result = stark::verify(&circuit, &proof, &pi);
    println!("Verification: {:?}", verify_result);
    println!();

    // 7. Multi-hop routing
    println!("--- Step 7: Multi-hop Route ---");
    let mut registry = AmmRegistry::new();
    let pool_ab = LiquidityPool::create(1, 2, 10_000, 50_000).unwrap();
    let pool_bc = LiquidityPool::create(2, 3, 50_000, 25_000).unwrap();
    registry.register_pool(pool_ab.clone());
    registry.register_pool(pool_bc.clone());

    let mut pools = vec![pool_ab, pool_bc];
    let route = find_route(&pools, 1, 3).unwrap();
    println!("Found route with {} hops", route.hops.len());

    let multi_result = execute_route(&mut pools, &route, 1000, 1).unwrap();
    println!(
        "Routed 1000 of asset 1 -> {} of asset 3 (total fees: {})",
        multi_result.final_amount, multi_result.total_fees
    );

    println!("\n=== Demo Complete ===");
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}
