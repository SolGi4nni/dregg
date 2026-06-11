//! End-to-end smoke test for the bot's real transfer path against a live node.
//!
//! Mirrors `DevnetClient::submit_transfer_turn`: derive a per-user
//! `AppCipherclerk` bound to the node's executor federation id, materialize the
//! sender + recipient cells via the faucet (with the sender's pubkey so the
//! cell carries a real verifying key), then submit a canonical SignedTurn to
//! `/api/turns/submit-signed`.
//!
//! Run against a local node:
//!   NODE_URL=http://127.0.0.1:8422 \
//!   FED_ID=<blake3(node_pubkey) hex> \
//!   cargo run -p dregg-discord-bot --example devnet_transfer_smoke

use dregg_app_framework::cipherclerk::AppCipherclerk;
use dregg_sdk::AgentCipherclerk;
use dregg_turn::Effect;
use zeroize::Zeroizing;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let base = std::env::var("NODE_URL").unwrap_or_else(|_| "http://127.0.0.1:8422".to_string());
    let bearer = std::env::var("BEARER").ok();

    let client = reqwest::Client::new();

    // Derive the executor federation id the same way the node does on a SOLO
    // node: blake3(node_operator_pubkey). On a full federated devnet this is the
    // configured federation id; the bot is given the matching FED_ID env.
    let fed: [u8; 32] = match std::env::var("FED_ID") {
        Ok(h) => hex::decode(&h)?
            .try_into()
            .expect("FED_ID must be 32 bytes"),
        Err(_) => {
            let id: serde_json::Value = client
                .get(format!("{base}/api/node/identity"))
                .send()
                .await?
                .json()
                .await?;
            let pk_hex = id
                .get("public_key")
                .and_then(|v| v.as_str())
                .expect("node identity");
            let pk: [u8; 32] = hex::decode(pk_hex)?.try_into().unwrap();
            *blake3::hash(&pk).as_bytes()
        }
    };
    println!("federation id: {}", hex::encode(fed));

    // Derive the sender cipherclerk (deterministic, like the bot does per user).
    let seed = Zeroizing::new(blake3::derive_key("dregg-discord-bot-v1", b"smoke-sender"));
    let agent = AgentCipherclerk::from_key_bytes(seed);
    let sender_pk = hex::encode(agent.public_key().0);
    let app = AppCipherclerk::new(agent, fed);
    let sender_cell = app.cell_id();
    let sender_cell_hex = hex::encode(sender_cell.0);

    let recipient_cell_hex =
        "4444444444444444444444444444444444444444444444444444444444444444".to_string();

    println!("sender cell:    {sender_cell_hex}");
    println!("sender pubkey:  {sender_pk}");
    println!("recipient cell: {recipient_cell_hex}");

    // Materialize sender cell WITH pubkey (so action sigs verify) + fund it.
    let faucet = |recipient: &str, pk: Option<&str>, amount: u64| {
        let mut body = serde_json::json!({ "recipient": recipient, "amount": amount });
        if let Some(pk) = pk {
            body["public_key"] = serde_json::json!(pk);
        }
        client.post(format!("{base}/api/faucet")).json(&body).send()
    };
    let r = faucet(&sender_cell_hex, Some(&sender_pk), 1000).await?;
    println!("faucet sender:    {}", r.text().await?);
    let r = faucet(&recipient_cell_hex, None, 0).await?;
    println!("faucet recipient: {}", r.text().await?);
    tokio::time::sleep(std::time::Duration::from_secs(3)).await;

    // Fetch sender nonce.
    let cell: serde_json::Value = client
        .get(format!("{base}/api/cell/{sender_cell_hex}"))
        .send()
        .await?
        .json()
        .await?;
    let nonce = cell.get("nonce").and_then(|n| n.as_u64()).unwrap_or(0);
    println!("sender nonce: {nonce}");

    // Build + sign a transfer turn (the bot's exact path).
    let recipient_cell = dregg_sdk::CellId(hex::decode(&recipient_cell_hex)?.try_into().unwrap());
    let action = app.make_action(
        sender_cell,
        "transfer",
        vec![Effect::Transfer {
            from: sender_cell,
            to: recipient_cell,
            amount: 250,
        }],
    );
    let mut turn = app.make_turn(action);
    turn.nonce = nonce;
    turn.fee = 500;
    let signed = app.sign_turn(&turn);
    let body = postcard::to_stdvec(&signed)?;
    println!("signed turn postcard bytes: {}", body.len());
    // Sanity: the bytes must round-trip back into the SAME SignedTurn type the
    // node deserializes (dregg_sdk::SignedTurn). If this fails, the wire format
    // diverged.
    match postcard::from_bytes::<dregg_sdk::SignedTurn>(&body) {
        Ok(rt) => println!(
            "local round-trip OK; signer={} action_count={}",
            hex::encode(rt.signer.0),
            rt.turn.call_forest.action_count()
        ),
        Err(e) => println!("LOCAL ROUND-TRIP FAILED: {e}"),
    }

    let mut req = client
        .post(format!("{base}/api/turns/submit-signed"))
        .header("content-type", "application/octet-stream")
        .body(body);
    if let Some(b) = &bearer {
        req = req.header("authorization", format!("Bearer {b}"));
    }
    let resp = req.send().await?;
    println!("submit status: {}", resp.status());
    println!("submit body:   {}", resp.text().await?);

    tokio::time::sleep(std::time::Duration::from_secs(3)).await;
    let recip: serde_json::Value = client
        .get(format!("{base}/api/cell/{recipient_cell_hex}"))
        .send()
        .await?
        .json()
        .await?;
    println!(
        "recipient balance after: {}",
        recip.get("balance").unwrap_or(&serde_json::Value::Null)
    );
    Ok(())
}
