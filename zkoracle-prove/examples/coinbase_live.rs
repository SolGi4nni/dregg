//! **coinbase_live** — the stranger-reusable demo: PROVE a REAL `api.coinbase.com` spot
//! price over genuine MPC-TLS, write the PORTABLE proof to a file, then RE-VERIFY it from the
//! file trusting only the pinned host + the published notary key (no trusted third party).
//!
//! Run (needs live network):
//! `cargo run -p dregg-zkoracle-prove --example coinbase_live --features tlsn-live --release -- BTC-USD`
//!
//! DEPENDS ON the portability patches (serde derives on `ZkOracleAttestation` and its members).
//! Without them the crate compiles but this example will not (the attestation is not `Serialize`).

use std::env;

use dregg_zkoracle_prove::endpoints::price::{prove_coinbase_live, verify_coinbase_live};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let asset = env::args().nth(1).unwrap_or_else(|| "BTC-USD".to_string());

    // ── PROVE: a genuine MPC-TLS 2PC session with api.coinbase.com, verified by a SEPARATE
    //    hosted notary (the notary co-derived the session keys, saw no plaintext). Returns the
    //    portable attestation + the notary's verifying key (the out-of-band trust anchor to
    //    publish alongside the proof).
    println!("proving a live api.coinbase.com spot price for {asset} …");
    let (att, notary_key) = prove_coinbase_live(&asset)?;

    // ── SERIALIZE: the proof file + the published notary pin.
    let proof_bytes = bincode::serialize(&att)?;
    let pin_bytes = bincode::serialize(&notary_key)?;
    std::fs::write("coinbase_proof.bin", &proof_bytes)?;
    std::fs::write("coinbase_notary.pin", &pin_bytes)?;
    println!(
        "wrote coinbase_proof.bin ({} bytes) + coinbase_notary.pin ({} bytes)",
        proof_bytes.len(),
        pin_bytes.len()
    );

    // ── VERIFY: a third party reloads the file + the published pin and re-checks the whole
    //    chain (real presentation.verify() against Coinbase's genuine cert chain via the
    //    Mozilla roots, notary pinned, host pinned, body well-formed, cross-leg weld), trusting
    //    no one. A tampered proof or a wrong notary key is refused here.
    let att2: dregg_zkoracle_prove::ZkOracleAttestation = bincode::deserialize(&proof_bytes)?;
    let key2: tlsn::attestation::signing::VerifyingKey = bincode::deserialize(&pin_bytes)?;
    let price = verify_coinbase_live(&att2, &key2)?;
    println!(
        "VERIFIED trustlessly from the file: {} = {} (session time t={})",
        price.asset, price.amount, price.time
    );
    Ok(())
}
