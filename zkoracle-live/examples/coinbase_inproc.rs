//! REAL coinbase MPC-TLS proof, in-process (prove + verify, no serialization) — proves
//! the hard thing first: a genuine live api.coinbase.com TLS session, attested + verified.
use dregg_zkoracle_prove::endpoints::price::{prove_coinbase_live, verify_coinbase_live};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let asset = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "BTC-USD".to_string());
    eprintln!("== proving a LIVE api.coinbase.com spot price for {asset} via MPC-TLS 2PC ...");
    let t = std::time::Instant::now();
    let (att, notary_key) = prove_coinbase_live(&asset)?;
    eprintln!("== proved in {:?}; verifying trustlessly ...", t.elapsed());
    let price = verify_coinbase_live(&att, &notary_key)?;
    println!(
        "VERIFIED: api.coinbase.com said {} = {} (session time t={})",
        price.asset, price.amount, price.time
    );
    Ok(())
}
