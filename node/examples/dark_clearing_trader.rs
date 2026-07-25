//! **THE REFERENCE TRADER.** Seal one order for a node's encrypted call auction.
//!
//! This is the client half of [`dregg_node::dark_clearing_service`], and it exists because the
//! node deliberately has no way to accept a plaintext order: the encryption and the signature
//! happen HERE, in the trader's own process, and only an opaque envelope crosses the wire.
//!
//! ```text
//!   # 1. the operator opens a session (four trader verifying keys, in seat order)
//!   curl -sX POST localhost:8420/api/market/dark-clearing/session \
//!        -H 'content-type: application/json' \
//!        -d "{\"traders\":[\"$PK0\",\"$PK1\",\"$PK2\",\"$PK3\"]}" > session.json
//!
//!   # 2. each trader seals its OWN order against the published collective key
//!   cargo run -p dregg-node --example dark_clearing_trader -- \
//!        session.json <seat> <bid|ask> <limit 0..3> <qty 0..15> <seed-hex> > order.b64
//!
//!   # 3. and submits the opaque envelope
//!   base64 -d < order.b64 | curl -sX POST --data-binary @- \
//!        -H 'content-type: application/octet-stream' \
//!        localhost:8420/api/market/dark-clearing/session/$SESSION/order
//! ```
//!
//! `<seed-hex>` is 64 hex characters of the trader's Ed25519 signing key. In a deployment it is
//! the trader's own key material and never leaves the trader's machine; on the command line it is
//! a demo affordance, and it is the reason this is an EXAMPLE and not a shipped tool.
//!
//! What this program proves, by construction: the plaintext `Order` is built here, consumed by
//! `encrypt_and_sign`, and is absent from the bytes printed on stdout.

use std::io::Write;

use base64::Engine as _;
use ed25519_dalek::SigningKey;
use fhegg_fhe::order_ingress::{OrderIngressSession, SignedOrderSubmission};
use fhegg_fhe::threshold::BfvParams;
use fhegg_fhe::{Order, Side};

use dregg_node::dark_clearing_service::{
    FAMILY_BUCKETS, FAMILY_MAX_QTY, collective_public_key_from_bytes,
};

fn die(message: &str) -> ! {
    eprintln!("dark_clearing_trader: {message}");
    std::process::exit(2);
}

fn hex32(s: &str) -> [u8; 32] {
    if s.len() != 64 {
        die("expected 64 hex characters");
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let hi = (chunk[0] as char)
            .to_digit(16)
            .unwrap_or_else(|| die("not hex"));
        let lo = (chunk[1] as char)
            .to_digit(16)
            .unwrap_or_else(|| die("not hex"));
        out[i] = ((hi << 4) | lo) as u8;
    }
    out
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 2 && args[1] == "--keygen" {
        // Convenience: mint a demo trader identity and print `seed_hex verifying_key_hex`.
        let mut seed = [0u8; 32];
        getrandom::fill(&mut seed).unwrap_or_else(|_| die("no OS entropy"));
        let key = SigningKey::from_bytes(&seed);
        println!(
            "{} {}",
            seed.iter().map(|b| format!("{b:02x}")).collect::<String>(),
            key.verifying_key()
                .to_bytes()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        );
        return;
    }
    if args.len() != 7 {
        die(
            "usage: dark_clearing_trader <session.json> <seat> <bid|ask> <limit> <qty> <seed-hex>\n\
             \tor: dark_clearing_trader --keygen",
        );
    }

    let session_json = std::fs::read_to_string(&args[1])
        .unwrap_or_else(|e| die(&format!("cannot read the session file: {e}")));
    let doc: serde_json::Value = serde_json::from_str(&session_json)
        .unwrap_or_else(|e| die(&format!("the session file is not JSON: {e}")));
    // Accept either the POST /session response envelope or the GET /session/{id} body.
    let session = if doc.get("session").and_then(|s| s.get("session")).is_some() {
        doc["session"].clone()
    } else {
        doc
    };

    let seat: usize = args[2]
        .parse()
        .unwrap_or_else(|_| die("seat must be an integer"));
    let side = match args[3].as_str() {
        "bid" => Side::Bid,
        "ask" => Side::Ask,
        _ => die("side must be `bid` or `ask`"),
    };
    let limit: usize = args[4]
        .parse()
        .unwrap_or_else(|_| die("limit must be an integer"));
    let qty: u16 = args[5]
        .parse()
        .unwrap_or_else(|_| die("qty must be an integer"));
    let signing_key = SigningKey::from_bytes(&hex32(&args[6]));

    // The family this surface is gated to. Refusing here saves a round trip and tells the trader
    // the same thing the node would: the bound is 4-bit, and the node checks only what the
    // envelope DECLARES.
    if limit >= FAMILY_BUCKETS {
        die(&format!("limit must be in 0..{FAMILY_BUCKETS}"));
    }
    if u64::from(qty) > FAMILY_MAX_QTY {
        die(&format!(
            "qty must be in 0..={FAMILY_MAX_QTY} (4-bit family)"
        ));
    }

    let params = BfvParams::fold_set();
    let pk_bytes = base64::engine::general_purpose::STANDARD
        .decode(
            session["collective_public_key_b64"]
                .as_str()
                .unwrap_or_else(|| die("the session carries no collective_public_key_b64")),
        )
        .unwrap_or_else(|e| die(&format!("collective_public_key_b64 is not base64: {e}")));
    let collective = collective_public_key_from_bytes(&pk_bytes, &params)
        .unwrap_or_else(|e| die(&format!("{e}")));
    let nonce = hex32(
        session["session"]
            .as_str()
            .unwrap_or_else(|| die("the session carries no session nonce")),
    );

    let ingress = OrderIngressSession::new(nonce, FAMILY_BUCKETS, &params, &collective)
        .unwrap_or_else(|e| die(&format!("the ingress session was refused: {e}")));

    // THE ONLY PLACE THE PLAINTEXT ORDER EXISTS. `encrypt_and_sign` consumes it; the envelope
    // below carries a BFV ciphertext and an Ed25519 attribution, and no order field.
    let order = Order { side, limit, qty };
    let (submission, _timing) = SignedOrderSubmission::encrypt_and_sign(
        &ingress,
        seat,
        0,
        &order,
        &params,
        &collective,
        &signing_key,
    )
    .unwrap_or_else(|e| die(&format!("trader-local sealing failed: {e}")));
    drop(order);

    let wire = submission.to_wire_bytes();
    eprintln!(
        "dark_clearing_trader: sealed {} bytes for seat {seat} (the order itself never leaves \
         this process)",
        wire.len()
    );
    let mut stdout = std::io::stdout();
    stdout
        .write_all(
            base64::engine::general_purpose::STANDARD
                .encode(&wire)
                .as_bytes(),
        )
        .and_then(|()| stdout.write_all(b"\n"))
        .unwrap_or_else(|e| die(&format!("stdout: {e}")));
}
