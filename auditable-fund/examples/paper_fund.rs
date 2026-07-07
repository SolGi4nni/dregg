//! A runnable auditable fund on the REAL attested price oracle: a modeled brain trades a
//! bounded mandate against a `CoinbaseSpotOracle` (every quote a re-verifiable
//! `ZkOracleAttestation` over a Coinbase spot session); every decision lands as an attested,
//! on-ledger turn; then a THIRD PARTY audits the track record — verifying the chain, the
//! decision attestations, EVERY fill's price attestation, and the mandate — and reports P&L.
//!
//! ⚑ PAPER-ONLY. Every fill is simulated against a real *attested* price. No exchange order,
//!   no custody, no real money. (The prices here ride the fixture-backed transport; the live
//!   `tlsn-live` roundtrip against `api.coinbase.com` is the same `PriceOracle` interface.)
//!
//! Run: `cargo run --manifest-path auditable-fund/Cargo.toml --example paper_fund`

use std::collections::HashMap;

use auditable_fund::{
    CoinbaseSpotOracle, EndpointConfig, FixtureNotary, Fund, Mandate, PriceOracle, ThresholdBrain,
    amount_to_cents, audit_fund, coinbase_spot_spec, verify_attested_price,
};

/// The pinned oracle notary seed — the fund and the auditor pin exactly this anchor.
const ORACLE_SEED: [u8; 32] = [0x11u8; 32];
const ASSET: &str = "BTC-USD";

/// A Coinbase spot oracle quoting `ASSET` at `amount` (decimal USD) at session `time`. Same
/// notary seed each round ⇒ the SAME pinned config across the whole run.
fn oracle_at(amount: &str, time: u64) -> CoinbaseSpotOracle {
    let notary = FixtureNotary::from_seed(&ORACLE_SEED);
    let quotes = HashMap::from([(ASSET.to_string(), amount.to_string())]);
    CoinbaseSpotOracle::new(notary, quotes, time)
}

/// The pinned oracle config (stable across rounds — deterministic in the seed).
fn oracle_config() -> EndpointConfig {
    EndpointConfig::new(
        coinbase_spot_spec(),
        FixtureNotary::from_seed(&ORACLE_SEED).verifying_key(),
    )
}

fn main() {
    println!("== The auditable fund — on REAL attested Coinbase spot prices (PAPER-ONLY) ==\n");

    // The mandate as caps: BTC-USD only, ≤ 8 units, 1_000_000 cents ($10k) budget, ≤ 20 turns.
    let mandate = Mandate {
        allowed_assets: vec![ASSET.to_string()],
        max_position: 8,
        budget: 1_000_000,
        max_turns: 20,
    };
    println!(
        "mandate: assets={:?} max_position={} budget={}c max_turns={}",
        mandate.allowed_assets, mandate.max_position, mandate.budget, mandate.max_turns
    );

    // FEDERATION SEAM: unset `DREGG_NODE_URL` ⇒ `NodeTarget::Local` (the in-process ledger,
    // default). Set it ⇒ each landed trade turn is ALSO submitted to that live node and
    // confirmed on its finalized receipt log; a rejected / non-landing submit fails the step
    // fail-closed. (`--features dregg-node-target/http` compiles the real HTTP transport.)
    let node_target = dregg_node_target::NodeTarget::from_env().expect("node target from env");
    if node_target.is_federation() {
        println!(
            "federation: routing every landed trade to {}\n",
            std::env::var(dregg_node_target::NODE_URL_ENV).unwrap_or_default()
        );
    }

    let oracle_config = oracle_config();
    let mut fund = Fund::open(
        "demo.fund.dregg",
        mandate,
        &[0x2au8; 32],
        oracle_config.clone(),
    )
    .expect("open")
    .with_node_target(node_target);
    let decision_config = fund.decision_config().clone();

    // A modeled momentum brain: buy under 950.00, sell over 1050.00 (thresholds in cents).
    let mut brain = ThresholdBrain {
        asset: ASSET.to_string(),
        buy_below: 95_000,
        sell_above: 105_000,
        qty: 2,
    };

    // A modeled price path over several rounds, quoted as REAL attested Coinbase spot prices.
    let path = [
        "900.00", "920.00", "1080.00", "1000.00", "940.00", "1100.00",
    ];
    for (round, amount) in path.iter().enumerate() {
        let oracle = oracle_at(amount, 1_700_000_000 + round as u64);
        // Show the fill price is itself re-verifiable: the auditor re-derives it from the notary.
        let attested = oracle.price(ASSET).expect("a quote");
        let reproven = verify_attested_price(&attested, &oracle_config).expect("re-verifies");
        match fund.step(&oracle, &mut brain) {
            Ok(o) => {
                let pos = if matches!(o.side, auditable_fund::Side::Hold) {
                    fund.position(ASSET)
                } else {
                    o.position_after
                };
                println!(
                    "round {round}: quote ${amount:<8} (attested→{reproven:>7}c, re-verified)  {:<4} -> cash={:>8}c BTC={pos}  turn={}",
                    format!("{:?}", o.side),
                    o.cash_after,
                    hex8(&o.turn_hash),
                );
                assert_eq!(reproven, amount_to_cents(amount).unwrap());
            }
            Err(e) => println!("round {round}: quote ${amount:<8}  REFUSED: {e}"),
        }
    }

    // ── The third-party audit ──
    println!("\n== third-party audit ==");
    let track = fund.export();
    match audit_fund(&track, &decision_config, &oracle_config) {
        Ok(report) => {
            println!(
                "chain: light-client VERIFIED ({} finalized turns)",
                report.turns
            );
            println!(
                "trades={} holds={}  final_cash={}c  open_positions={:?}",
                report.trades, report.holds, report.final_cash, report.open_positions
            );
            println!(
                "mark_to_market={}c  equity={}c  total_pnl={}c  (realized_pnl={}c)",
                report.mark_to_market, report.equity, report.total_pnl, report.realized_pnl
            );
            println!(
                "\nEVERY decision attested, EVERY fill at a REAL zkOracle-attested Coinbase price,\nmandate held EVERY turn — audited, not trusted."
            );
        }
        Err(e) => println!("AUDIT FAILED: {e}"),
    }
}

fn hex8(h: &[u8; 32]) -> String {
    h[..4].iter().map(|b| format!("{b:02x}")).collect()
}
