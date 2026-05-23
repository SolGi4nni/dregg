//! Full CDP stablecoin lifecycle demonstration.
//!
//! This example demonstrates:
//! 1. Deploying the CDP circuit to the program registry
//! 2. Opening a collateral position
//! 3. Minting stablecoins with a STARK proof of collateral ratio
//! 4. Price drop making a position liquidatable
//! 5. Liquidation execution
//!
//! Run with: `cargo run -p pyana-stablecoin --example demo`

use pyana_cell::CellId;
use pyana_dsl_runtime::ProgramRegistry;
use pyana_stablecoin::{
    CollateralPosition, ETH_ASSET_TYPE, LiquidationEngine, MIN_RATIO_BPS, PriceOracle,
    StablecoinRegistry, cdp_cell_program, deploy_cdp_program, test_attestation,
};

fn main() {
    println!("=== Pyana CDP Stablecoin Demo ===\n");

    // --- Setup ---
    let oracle_key = [0x01u8; 32];
    let mut oracle = PriceOracle::new(vec![oracle_key], 1000);
    let mut registry = StablecoinRegistry::new();
    let mut program_registry = ProgramRegistry::new();
    let engine = LiquidationEngine::default_config();

    // Deploy the CDP circuit
    let vk_hash = deploy_cdp_program(&mut program_registry).unwrap();
    println!(
        "[1] CDP circuit deployed. VK hash: {:02x}{:02x}{:02x}{:02x}...",
        vk_hash[0], vk_hash[1], vk_hash[2], vk_hash[3]
    );

    // --- Oracle provides initial price ---
    let price_eth = 2000u64; // $2000 per ETH
    let attestation = test_attestation("ETH/USD", price_eth, 100, oracle_key);
    oracle.submit_attestation(attestation.clone(), 105).unwrap();
    println!("[2] Oracle price: ETH/USD = ${price_eth}");

    // --- Alice opens a CDP ---
    let alice = CellId([0xAA; 32]);
    let mut position = CollateralPosition::open(
        alice,
        100, // 100 ETH collateral
        ETH_ASSET_TYPE,
        MIN_RATIO_BPS, // 150% minimum ratio
        200,           // opened at block 200
    )
    .unwrap();
    registry.register(position.clone());
    println!("[3] Alice opens CDP with 100 ETH collateral");
    println!(
        "    Position ID: {:02x}{:02x}{:02x}{:02x}...",
        position.id[0], position.id[1], position.id[2], position.id[3]
    );

    // --- Alice mints PUSD ---
    let mint_amount = 100_000u64; // Mint $100k PUSD
    let transition = position.mint(mint_amount, &attestation, 105, 1000).unwrap();
    registry.update(&position);
    registry.record_mint(mint_amount);

    println!("[4] Alice mints {mint_amount} PUSD");
    println!(
        "    Collateral value: {} * {} = ${}",
        100,
        price_eth,
        100 * price_eth
    );
    println!(
        "    Collateral ratio: {}%",
        position.collateral_ratio_bps(price_eth).unwrap() / 100
    );
    println!("    STARK proof size: {} bytes", transition.proof.len());
    println!("    Total PUSD supply: {}", registry.total_supply);

    // Verify the proof through the program registry
    let _program = cdp_cell_program(); // kept to show it's available
    let witness = pyana_stablecoin::CdpWitness {
        collateral_amount: 100,
        price: price_eth,
        debt_amount: mint_amount,
        ratio_bps: MIN_RATIO_BPS,
        position_id: position.id,
        oracle_commitment: attestation.commitment(),
        price_timestamp: 100,
        max_age: 1000,
    };
    let public_inputs = witness.public_inputs();
    let verify = program_registry.verify_with_program(&vk_hash, &public_inputs, &transition.proof);
    println!("    Proof verified via registry: {}", verify.is_ok());

    // --- Price drops ---
    let new_price = 1200u64; // Price crashes to $1200
    let low_attestation = test_attestation("ETH/USD", new_price, 500, oracle_key);
    oracle
        .submit_attestation(low_attestation.clone(), 505)
        .unwrap();

    println!("\n[5] PRICE DROP: ETH/USD = ${new_price}");
    println!(
        "    Alice's new ratio: {}%",
        position.collateral_ratio_bps(new_price).unwrap() / 100
    );
    println!(
        "    Position liquidatable: {}",
        position.is_liquidatable(new_price)
    );

    // --- Bob liquidates ---
    let bob = CellId([0xBB; 32]);
    let liquidatable = engine.scan_liquidatable(&registry, ETH_ASSET_TYPE, new_price);
    println!(
        "\n[6] Liquidation scan: {} positions at risk",
        liquidatable.len()
    );

    let result = engine
        .liquidate(&mut position, bob, new_price, 600)
        .unwrap();
    registry.update(&position);
    registry.record_burn(result.debt_repaid);

    println!("[7] Bob liquidates Alice's position:");
    println!("    Debt repaid: {} PUSD", result.debt_repaid);
    println!(
        "    Collateral seized by Bob: {} ETH (value: ${})",
        result.collateral_seized,
        result.collateral_seized as u64 * new_price
    );
    println!(
        "    Collateral returned to Alice: {} ETH",
        result.collateral_returned
    );
    println!(
        "    Bob's profit (liquidation bonus): ~${:.0}",
        (result.collateral_seized as f64 * new_price as f64) - result.debt_repaid as f64
    );
    println!("    Total PUSD supply: {}", registry.total_supply);

    println!("\n=== Demo Complete ===");
}
