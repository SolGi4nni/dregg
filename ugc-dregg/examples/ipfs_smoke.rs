//! `ipfs_smoke` — the live IPFS-join smoke driver (deploy/ipfs/RUNBOOK-IPFS.md).
//!
//! Against a RUNNING local kubo daemon (loopback RPC + gateway, the
//! `kubo-hbox.service` shape), this drives the real join end to end:
//!
//! 1. publish a deterministic daily universe through the Kubo RPC
//!    ([`ugc_dregg::ipfs::publish_universe`] over `KuboClient` + the std-only
//!    `StdHttpPost` — no TLS, loopback only);
//! 2. fetch it back through the SAME daemon's block API, verified
//!    (CID re-witness + UniverseId re-derivation + expected-id check);
//! 3. fetch it back through the LOCAL HTTP GATEWAY as a trustless `?format=raw`
//!    block read (`GatewayClient`) — the same verified path a stranger's gateway
//!    read takes;
//! 4. print the CID + a public-gateway URL for the manual cross-check.
//!
//! Env: `DREGG_IPFS_API` (default `http://127.0.0.1:5001`), `DREGG_IPFS_GATEWAY`
//! (default `http://127.0.0.1:8080`).
//!
//! Exit code 0 = every verified step passed.

use dregg_ipfs::client::{GatewayClient, KuboClient, StdHttpPost};
use ugc_dregg::Universe;
use ugc_dregg::ipfs::{fetch_universe, publish_universe};

fn main() {
    let api = std::env::var("DREGG_IPFS_API").unwrap_or_else(|_| "http://127.0.0.1:5001".into());
    let gw = std::env::var("DREGG_IPFS_GATEWAY").unwrap_or_else(|_| "http://127.0.0.1:8080".into());

    // A deterministic, procgen-committed universe: anyone re-running this smoke
    // derives the identical universe, id, and CID.
    let epoch = *blake3::hash(b"dregg-ipfs-smoke/epoch-1").as_bytes();
    let universe = Universe::daily("ipfs-smoke", &epoch).expect("daily universe publishes");
    let id = universe.id();
    println!("universe        : {} ({})", universe.name(), id);

    // 1. PUBLISH through the Kubo RPC.
    let kubo = KuboClient::new(api.clone(), StdHttpPost::new());
    let receipt = publish_universe(&kubo, &universe).expect("publish over the Kubo RPC");
    println!(
        "payload pinned  : {} ({} bytes)",
        receipt.payload_cid, receipt.payload_len
    );

    // 2. FETCH BACK via the daemon's block API — verified (CID re-witness, id
    // re-derived from content, expected-id checked).
    let back = fetch_universe(&kubo, &receipt.payload_cid, Some(&id))
        .expect("verified fetch via the Kubo block API");
    assert_eq!(back.id(), id);
    println!("rpc fetch       : verified, id re-derived OK");

    // 3. FETCH BACK via the local HTTP gateway — the trustless raw-block read.
    let gateway = GatewayClient::new(gw.clone(), StdHttpPost::new());
    let back = fetch_universe(&gateway, &receipt.payload_cid, Some(&id))
        .expect("verified fetch via the local gateway (?format=raw)");
    assert_eq!(back.id(), id);
    println!("gateway fetch   : verified, id re-derived OK");

    // 4. The public-gateway cross-check is manual (propagation takes minutes and
    // depends on the swarm/DHT):
    println!(
        "public check    : curl -L https://ipfs.io/ipfs/{}",
        receipt.payload_cid
    );
    println!("ok");
}
