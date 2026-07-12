//! End-to-end driven test of the DUAL-ASSET ($DREGG + USDC) payment model on the
//! MOCK/devnet path — NO real funds, NO network, mock price oracle.
//!
//! Drives ember's economics exactly:
//!   * a USDC payment credits runs at the flat $0.10 and lands in the FUEL tank;
//!   * a $DREGG payment credits runs at the price-fed 20%-discounted rate and lands
//!     in the PILE;
//!   * spend_inference_usd draws down the USDC fuel and FAILS CLOSED when empty
//!     (the "must refuel" signal) — even though a $DREGG-paid run still burns fuel;
//!   * the OTC desk quotes $DREGG-out for USDC-in at 10% off, refused when the pile
//!     is short;
//!   * non-vacuous: an unknown mint is refused; a $DREGG-paid run only grows the pile.
//!
//! Run: `cargo test -p dregg-pay --test dual_asset_e2e -- --nocapture`.

use dregg_pay::{
    Asset, CreditLedger, CreditOutcome, DepositAddress, InMemoryStore, InMemoryTreasuryStore,
    MockOracle, OtcError, PayConfig, Treasury, UserId, otc_quote, runs_for_payment,
};

#[test]
fn dual_asset_treasury_pricing_otc_driven_end_to_end() {
    // ── config: THROWAWAY seed, MOCK $DREGG + MOCK USDC mints (never mainnet) ──
    let seed = *b"dregg-pay DUAL-ASSET throwaway seed - not real!!";
    let dregg_mint = [0x11u8; 32];
    let treasury_addr = DepositAddress([0xEEu8; 32]);
    let mut config = PayConfig::devnet_mock(seed, dregg_mint, treasury_addr, 1_000_000);
    let usdc_mint = [0x22u8; 32];
    config.usdc_mint = usdc_mint;
    // ember's economics, explicit for the record:
    config.price_usd_per_run = 0.10; // $0.10 / run
    config.dregg_discount_bps = 2000; // 20% holder discount on $DREGG runs
    config.otc_discount_bps = 1000; // 10% OTC discount
    config.usdc_decimals = 6;
    config.dregg_decimals = 6;

    // Mock oracle: $DREGG = $0.005 (a live Jupiter quote in prod).
    let oracle = MockOracle::new(0.005);

    println!("\n=== dregg-pay DUAL-ASSET — driven end-to-end (mock/devnet) ===");
    println!("network              : {:?}", config.network);
    println!("price_usd_per_run    : ${:.2}", config.price_usd_per_run);
    println!("dregg_discount        : {} bps", config.dregg_discount_bps);
    println!("otc_discount          : {} bps", config.otc_discount_bps);
    println!("$DREGG price (mock)  : $0.005 / whole $DREGG");

    // ── asset routing: mints resolve to assets, unknown fails closed ──
    assert_eq!(config.asset_for_mint(&dregg_mint), Some(Asset::Dregg));
    assert_eq!(config.asset_for_mint(&usdc_mint), Some(Asset::Usdc));
    assert_eq!(
        config.asset_for_mint(&[0x99u8; 32]),
        None,
        "unknown mint refused"
    );

    let ledger = CreditLedger::new(InMemoryStore::new(), config.price_per_run);
    let treasury = Treasury::new(InMemoryTreasuryStore::new(), config.usdc_decimals);
    let alice = UserId::from("alice");
    let bob = UserId::from("bob");

    // ── 1. USDC payment: flat $0.10, lands in the FUEL tank ──
    // Alice pays $1.00 = 1_000_000 atomic USDC → 10 runs.
    let usdc_amount = 1_000_000u64;
    let usdc_runs = runs_for_payment(Asset::Usdc, usdc_amount, &oracle, &config).unwrap();
    println!("\n-- USDC payment (the FUEL) --");
    println!("alice pays {usdc_amount} atomic USDC ($1.00) → {usdc_runs} runs @ $0.10");
    assert_eq!(usdc_runs, 10, "$1.00 / $0.10 = 10 runs");
    let usdc_pay = mk_payment("alice", Asset::Usdc, usdc_amount, "usdc-tx1");
    assert!(matches!(
        ledger.credit_runs(&usdc_pay, usdc_runs),
        CreditOutcome::Credited { runs: 10, .. }
    ));
    treasury.record_payment(Asset::Usdc, usdc_amount);
    assert_eq!(ledger.balance(&alice), 10);
    assert_eq!(treasury.usdc_balance(), 1_000_000, "USDC → fuel tank");
    assert_eq!(treasury.dregg_balance(), 0, "USDC did NOT touch the pile");

    // ── 2. $DREGG payment: price-fed 20% discount, lands in the PILE ──
    // Bob pays 100 whole $DREGG = 100_000_000 atomic. USD value $0.50.
    // Discounted per-run = $0.08 → $0.50/$0.08 = 6.25 → 6 runs (5 at flat — reward).
    let dregg_amount = 100_000_000u64;
    let dregg_runs = runs_for_payment(Asset::Dregg, dregg_amount, &oracle, &config).unwrap();
    println!("\n-- $DREGG payment (the PILE) --");
    println!(
        "bob pays {dregg_amount} atomic $DREGG (100 whole, $0.50) → {dregg_runs} runs @ $0.08"
    );
    assert_eq!(
        dregg_runs, 6,
        "$0.50 / $0.08 = 6 runs (vs 5 flat — holder reward)"
    );
    assert_eq!(
        runs_for_payment(Asset::Usdc, 500_000, &oracle, &config).unwrap(),
        5,
        "same $0.50 in USDC gives only 5 — the discount is real"
    );
    let dregg_pay = mk_payment("bob", Asset::Dregg, dregg_amount, "dregg-tx1");
    assert!(matches!(
        ledger.credit_runs(&dregg_pay, dregg_runs),
        CreditOutcome::Credited { runs: 6, .. }
    ));
    treasury.record_payment(Asset::Dregg, dregg_amount);
    assert_eq!(ledger.balance(&bob), 6);
    assert_eq!(treasury.dregg_balance(), 100_000_000, "$DREGG → the pile");
    assert_eq!(
        treasury.usdc_balance(),
        1_000_000,
        "pile grew, fuel unchanged"
    );

    // ── idempotency: re-crediting either payment does not double-credit ──
    assert_eq!(
        ledger.credit_runs(&usdc_pay, usdc_runs),
        CreditOutcome::AlreadyCredited
    );
    assert_eq!(ledger.balance(&alice), 10);

    // ── 3. inference burns USD FUEL and fails closed when the tank is dry ──
    println!("\n-- inference draws down the FUEL (every run, either asset) --");
    let cost_usd = 0.01; // ~Bedrock cost
    // 16 runs were credited (10 USDC + 6 $DREGG). Each burns ~$0.01 fuel.
    // Fuel tank holds $1.00 = 100 inferences of $0.01, so all 16 runs are funded.
    let mut fuel = treasury.usdc_balance();
    for i in 0..16 {
        fuel = treasury
            .spend_inference_usd(cost_usd)
            .unwrap_or_else(|e| panic!("run {i} should be funded: {e}"));
    }
    println!("16 runs funded; fuel now {fuel} atomic USDC");
    assert_eq!(fuel, 1_000_000 - 16 * 10_000, "16 × $0.01 burned");
    // The pile is untouched by inference — it is not fuel.
    assert_eq!(
        treasury.dregg_balance(),
        100_000_000,
        "pile untouched by inference"
    );

    // Drain the tank to prove the fail-closed refuel signal.
    let remaining_inferences = fuel / 10_000;
    for _ in 0..remaining_inferences {
        treasury.spend_inference_usd(cost_usd).unwrap();
    }
    let err = treasury.spend_inference_usd(cost_usd).unwrap_err();
    println!("tank dry → refuel signal: {err}");
    assert!(
        matches!(err, dregg_pay::TreasuryError::InsufficientFuel { .. }),
        "empty tank fails closed"
    );

    // ── 4. OTC desk: bring USDC, buy $DREGG from the pile at 10% off ──
    println!("\n-- OTC quote (bring USDC, buy $DREGG at 10% off) --");
    let pile = treasury.dregg_balance(); // 100_000_000 atomic
    // Bring $0.10 = 100_000 atomic USDC. Effective price $0.0045.
    // dregg_out = 0.10 / 0.0045 = 22.22 whole → 22_222_222 atomic. Pile covers it.
    let quote = otc_quote(100_000, pile, &oracle, &config).expect("pile covers the fill");
    println!(
        "bring 100000 atomic USDC → {} atomic $DREGG @ ${:.4}/$DREGG (mid ${:.4})",
        quote.dregg_out, quote.effective_price_usd, quote.oracle_price_usd
    );
    assert!((quote.effective_price_usd - 0.0045).abs() < 1e-9);
    assert_eq!(quote.dregg_out, 22_222_222);
    // At market (no discount) they'd get only 20_000_000 — the buyer gets more.
    assert!(
        quote.dregg_out > 20_000_000,
        "10% off gives the buyer more $DREGG"
    );

    // A fill larger than the pile is refused with the precise shortfall.
    let big = otc_quote(10_000_000, pile, &oracle, &config).unwrap_err();
    println!("oversized fill refused: {big}");
    match big {
        OtcError::InsufficientPile { needed, available } => {
            assert!(needed > available);
            assert_eq!(available, pile);
        }
        other => panic!("expected InsufficientPile, got {other:?}"),
    }

    // bob is not alice — attribution held across the whole flow.
    assert_eq!(ledger.balance(&bob), 6);

    println!(
        "\n=== dual-asset invariants held: USDC→fuel@flat, $DREGG→pile@discount, \
         fuel fail-closed, OTC 10%-off + precise refusal ===\n"
    );
}

fn mk_payment(
    user: &str,
    asset: Asset,
    amount: u64,
    reference: &str,
) -> dregg_pay::PaymentReceived {
    dregg_pay::PaymentReceived {
        user: UserId::from(user),
        deposit_address: DepositAddress([0u8; 32]),
        asset,
        amount,
        reference: dregg_pay::PaymentRef(reference.to_string()),
    }
}
