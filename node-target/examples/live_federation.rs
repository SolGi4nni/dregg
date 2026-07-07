//! Drive the fleet's REAL `HttpNode` transport against a LIVE `dregg-node` federation.
//!
//! This is the fleet's own federation-routing code (`dregg_node_target::HttpNode`,
//! `FederationSink`) exercised against real iron — not the in-memory `StubNode`. It runs
//! the two legs of `NodeTarget::route` separately so each is observable:
//!
//!   * the **receipt / light-client leg** (`landed`): confirm a turn hash is on the node's
//!     finalized `GET /api/receipts` log — the membership check a light client makes;
//!   * the **submit leg** (`submit`): offer a commitment to `POST /turn/submit`.
//!
//! Usage (requires the `http` feature):
//!   DREGG_NODE_URL=http://192.168.50.39:8420 \
//!   DREGG_PEER_URL=http://192.168.50.130:8420 \
//!   LANDED_HASH=<64-hex turn_hash known-final on the node> \
//!   cargo run -p dregg-node-target --features http --example live_federation
//!
//! DREGG_NODE_BEARER, if set, is sent as `Authorization: Bearer` on the submit (the real
//! node gates `/turn/submit` behind `require_auth` once a passphrase is set).

#[cfg(not(feature = "http"))]
fn main() {
    eprintln!("build with --features http to run the live federation probe");
    std::process::exit(2);
}

#[cfg(feature = "http")]
fn main() {
    use dregg_node_target::{FederationSink, HttpNode, SubmittedTurn};

    let node_url =
        std::env::var("DREGG_NODE_URL").unwrap_or_else(|_| "http://192.168.50.39:8420".into());
    let peer_url = std::env::var("DREGG_PEER_URL").ok();
    let landed_hash = std::env::var("LANDED_HASH").ok();

    fn parse_hash(h: &str) -> [u8; 32] {
        let b = hex::decode(h.trim()).expect("64-hex turn hash");
        b.try_into().expect("32 bytes")
    }

    println!("== fleet HttpNode vs LIVE dregg-node federation ==");
    println!("primary node : {node_url}");
    if let Some(p) = &peer_url {
        println!("peer node    : {p}");
    }

    let node = HttpNode::new(&node_url).expect("http node");

    // ── Leg 1: the receipt / light-client membership check against real iron. ──
    if let Some(h) = &landed_hash {
        let hash = parse_hash(h);
        let here = node.landed(&hash).expect("landed query");
        println!("\n[landed] turn {h}");
        println!("  present on primary ({node_url}): {here}");
        if let Some(p) = &peer_url {
            let peer = HttpNode::new(p).expect("peer http node");
            let there = peer.landed(&hash).expect("peer landed query");
            println!("  present on peer    ({p}): {there}");
            if here && there {
                println!("  => CROSS-NODE PRESENT + light-client-verified on both nodes");
            } else if here {
                println!("  => present on primary only (not replicated to peer's receipt log)");
            }
        }
    }

    // A hash that is NOT on the log must read false (fail-closed negative).
    let absent = [0xABu8; 32];
    println!(
        "\n[landed] a never-submitted hash reads present={}  (expected false)",
        node.landed(&absent).unwrap_or(true)
    );

    // ── Leg 2: the submit leg. Offer a fresh commitment to POST /turn/submit. ──
    let mut commitment = [0u8; 32];
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos()
        .to_le_bytes();
    commitment[..16].copy_from_slice(&stamp);
    let turn = SubmittedTurn::new("depth.crown.fleet", commitment);
    println!(
        "\n[submit] POST /turn/submit  commitment={}",
        hex::encode(commitment)
    );
    match node.submit(&turn) {
        Ok(landed) => println!(
            "  ACCEPTED — node turn_hash {}",
            hex::encode(landed.node_turn_hash)
        ),
        Err(e) => println!("  REFUSED (fail-closed): {e}"),
    }
}
