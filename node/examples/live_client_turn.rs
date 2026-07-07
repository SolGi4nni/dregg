//! live_client_turn.rs — THE CAPSTONE SUBMITTER.
//!
//! A FRESH external client (a brand-new Ed25519 identity that NO node has ever seen — no
//! pre-existing cell) builds and signs its OWN Transfer turn and submits it, over HTTP, to
//! a LIVE `dregg-node` on a running cross-machine VERIFIED federation. It then watches the
//! turn STREAM-FINALIZE cross-node: the client's default cell is provisioned + funded, its
//! own signed Transfer's destination materialises with the transferred balance, and each
//! node's attested `latest_height` advances — witnessed on BOTH machines when
//! `DREGG_PEER_URL` is set.
//!
//! This is the exact client-turn flow of `node/tests/payoff_client_turn.rs`, lifted out of
//! the test's self-spawned local federation and pointed at a real, already-running node
//! over the network. The HTTP helpers are the same raw-TCP `http_get` / `http_post` the
//! test uses, generalized to an arbitrary `host:port` parsed from a base URL.
//!
//! Env:
//!   * `DREGG_NODE_URL`    — the node to submit to (default http://192.168.50.39:8420).
//!   * `DREGG_PEER_URL`    — optional: the OTHER machine, to confirm CROSS-MACHINE finality.
//!   * `DREGG_NODE_BEARER` — the operator bearer token for the protected `/turns/submit`
//!                           route (the node's `/cipherclerk/unlock` response). Unset ⇒ no
//!                           auth header (accepted only by a node with no passphrase set).
//!   * `DREGG_AMOUNT`      — the faucet fund amount (default 5000). The client transfers a
//!                           fifth of it (default 1000) to the fresh destination.
//!
//! Run (against the live cross-machine federation):
//!   DREGG_NODE_URL=http://192.168.50.39:8420 \
//!   DREGG_PEER_URL=http://192.168.50.130:8420 \
//!   DREGG_NODE_BEARER=<bearer> \
//!     cargo run -p dregg-node --example live_client_turn

use std::io::{Read, Write};
use std::net::TcpStream;
use std::time::{Duration, Instant};

use dregg_sdk::AgentCipherclerk as CipherClerk;
use dregg_turn::action::Effect;

/// A node endpoint parsed from a base URL: `(host, port)`.
#[derive(Clone)]
struct Endpoint {
    label: String,
    host: String,
    port: u16,
}

/// Parse `http://host:port` (or `host:port`, or bare `host` defaulting to :8420) into an
/// [`Endpoint`]. Trailing paths / slashes are ignored — only the authority is used.
fn parse_endpoint(label: &str, url: &str) -> Endpoint {
    let s = url.trim();
    let s = s
        .strip_prefix("http://")
        .or_else(|| s.strip_prefix("https://"))
        .unwrap_or(s);
    // Drop any path after the authority.
    let authority = s.split('/').next().unwrap_or(s);
    let (host, port) = match authority.rsplit_once(':') {
        Some((h, p)) => (h.to_string(), p.parse::<u16>().unwrap_or(8420)),
        None => (authority.to_string(), 8420u16),
    };
    Endpoint {
        label: label.to_string(),
        host,
        port,
    }
}

/// GET `path` from `(host, port)`; returns the response BODY (after the header break).
fn http_get(ep: &Endpoint, path: &str) -> Option<String> {
    let mut stream = TcpStream::connect((ep.host.as_str(), ep.port)).ok()?;
    stream.set_read_timeout(Some(Duration::from_secs(6))).ok()?;
    stream
        .set_write_timeout(Some(Duration::from_secs(6)))
        .ok()?;
    let req = format!(
        "GET {path} HTTP/1.1\r\nHost: {}:{}\r\nConnection: close\r\n\r\n",
        ep.host, ep.port
    );
    stream.write_all(req.as_bytes()).ok()?;
    let mut buf = String::new();
    stream.read_to_string(&mut buf).ok()?;
    Some(buf.split_once("\r\n\r\n")?.1.to_string())
}

/// POST raw bytes with an explicit content-type + optional bearer; returns the FULL raw
/// response (status line + headers + body) so a non-2xx status is visible.
fn http_post(
    ep: &Endpoint,
    path: &str,
    content_type: &str,
    bearer: Option<&str>,
    body: &[u8],
) -> Option<String> {
    let mut stream = TcpStream::connect((ep.host.as_str(), ep.port)).ok()?;
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .ok()?;
    stream
        .set_write_timeout(Some(Duration::from_secs(10)))
        .ok()?;
    let auth = match bearer {
        Some(tok) => format!("Authorization: Bearer {tok}\r\n"),
        None => String::new(),
    };
    let head = format!(
        "POST {path} HTTP/1.1\r\nHost: {}:{}\r\nContent-Type: {content_type}\r\n\
         {auth}Content-Length: {}\r\nConnection: close\r\n\r\n",
        ep.host,
        ep.port,
        body.len()
    );
    stream.write_all(head.as_bytes()).ok()?;
    stream.write_all(body).ok()?;
    let mut buf = Vec::new();
    stream.read_to_end(&mut buf).ok()?;
    Some(String::from_utf8_lossy(&buf).to_string())
}

/// Extract a flat top-level JSON field's raw token (no serde_json dep).
fn json_field<'a>(body: &'a str, field: &str) -> Option<&'a str> {
    let key = format!("\"{field}\":");
    let start = body.find(&key)? + key.len();
    let rest = body[start..].trim_start();
    if let Some(stripped) = rest.strip_prefix('"') {
        let end = stripped.find('"')?;
        Some(&stripped[..end])
    } else {
        let end = rest.find([',', '}']).unwrap_or(rest.len());
        Some(rest[..end].trim())
    }
}

fn latest_height(ep: &Endpoint) -> u64 {
    http_get(ep, "/status")
        .and_then(|b| json_field(&b, "latest_height").map(|s| s.to_string()))
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0)
}

/// The federation id the executor verifies action signatures against. On a configured
/// federation `federation_id_for_executor` returns the genesis `federation_id`, which the
/// public `/api/membership` endpoint serves. The client MUST sign its action over this id.
fn fetch_federation_id(ep: &Endpoint) -> Option<[u8; 32]> {
    let body = http_get(ep, "/api/membership")?;
    let hex = json_field(&body, "federation_id")?;
    hex_decode_32(hex)
}

/// `(found, balance)` for a cell id via the public `/api/cell/{id}` endpoint.
fn cell_balance(ep: &Endpoint, cell_hex: &str) -> (bool, u64) {
    let Some(body) = http_get(ep, &format!("/api/cell/{cell_hex}")) else {
        return (false, 0);
    };
    let found = json_field(&body, "found") == Some("true");
    let bal = json_field(&body, "balance")
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0);
    (found, bal)
}

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, o) in out.iter_mut().enumerate() {
        *o = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}

fn env_or(key: &str, default: &str) -> String {
    std::env::var(key)
        .ok()
        .map(|v| v.trim().to_string())
        .filter(|v| !v.is_empty())
        .unwrap_or_else(|| default.to_string())
}

fn main() {
    // ── Config ──
    let node = parse_endpoint(
        "node",
        &env_or("DREGG_NODE_URL", "http://192.168.50.39:8420"),
    );
    let peer = std::env::var("DREGG_PEER_URL")
        .ok()
        .map(|v| v.trim().to_string())
        .filter(|v| !v.is_empty())
        .map(|u| parse_endpoint("peer", &u));
    let bearer = std::env::var("DREGG_NODE_BEARER")
        .ok()
        .map(|v| v.trim().to_string())
        .filter(|v| !v.is_empty());
    let fund_amount: u64 = env_or("DREGG_AMOUNT", "5000").parse().unwrap_or(5000);
    let transfer_amount: u64 = (fund_amount / 5).max(1);
    // Fee: >= a Transfer's computron cost (~300) and well under the funded balance.
    let fee: u64 = (fund_amount / 5)
        .max(1_000)
        .min(fund_amount.saturating_sub(transfer_amount + 1));
    let timeout_s: u64 = 120;

    // All endpoints we witness finality on.
    let mut witnesses: Vec<Endpoint> = vec![node.clone()];
    if let Some(p) = &peer {
        witnesses.push(p.clone());
    }

    println!("[live] node  = http://{}:{}", node.host, node.port);
    match &peer {
        Some(p) => println!("[live] peer  = http://{}:{}", p.host, p.port),
        None => println!(
            "[live] peer  = (none — single-node witness; set DREGG_PEER_URL for cross-machine)"
        ),
    }
    println!(
        "[live] fund={fund_amount} transfer={transfer_amount} fee={fee} bearer={}",
        if bearer.is_some() { "set" } else { "UNSET" }
    );

    // ── The federation id the executor verifies signatures against ──
    let federation_id = match fetch_federation_id(&node) {
        Some(id) => id,
        None => {
            eprintln!(
                "[live] FATAL: could not read federation_id from {}:{} /api/membership — is the node up?",
                node.host, node.port
            );
            std::process::exit(2);
        }
    };
    println!("[live] federation id = {}", hex_encode(&federation_id));

    // ── A FRESH external client identity (a brand-new random keypair — no node has it) ──
    let client = CipherClerk::new();
    let client_pubkey = client.public_key();
    let actor_cell = client.cell_id("default");
    let actor_hex = hex_encode(&actor_cell.0);
    let signer_hex = hex_encode(&client_pubkey.0);
    println!("[live] fresh client signer = {signer_hex}");
    println!("[live] client actor cell   = {actor_hex}");

    // A FRESH destination — another brand-new identity's default cell.
    let dest = CipherClerk::new();
    let dest_cell = dest.cell_id("default");
    let dest_hex = hex_encode(&dest_cell.0);
    println!("[live] destination cell    = {dest_hex}");

    // ── STEP 1: faucet-fund the client's cell (an external client has no genesis balance;
    //    a real turn costs computrons paid from balance). Poll until funded cross-node. ──
    let faucet_body = format!("{{\"recipient\":\"{actor_hex}\",\"amount\":{fund_amount}}}");
    let faucet_resp = match http_post(
        &node,
        "/api/faucet",
        "application/json",
        None,
        faucet_body.as_bytes(),
    ) {
        Some(r) => r,
        None => {
            eprintln!("[live] FATAL: POST /api/faucet did not reach the node");
            std::process::exit(2);
        }
    };
    if !faucet_resp.contains("\"success\":true") {
        eprintln!("[live] FATAL: faucet grant was not accepted; response:\n{faucet_resp}");
        std::process::exit(2);
    }
    println!("[live] faucet-funded the client cell with {fund_amount}; awaiting cross-node…");

    let fund_deadline = Instant::now() + Duration::from_secs(timeout_s);
    let mut funded_everywhere = false;
    while Instant::now() < fund_deadline {
        std::thread::sleep(Duration::from_secs(2));
        if witnesses
            .iter()
            .all(|ep| cell_balance(ep, &actor_hex) == (true, fund_amount))
        {
            funded_everywhere = true;
            break;
        }
    }
    if !funded_everywhere {
        let per: Vec<_> = witnesses
            .iter()
            .map(|ep| (ep.label.clone(), cell_balance(ep, &actor_hex)))
            .collect();
        eprintln!("[live] FATAL: faucet grant did not fund the client cell everywhere: {per:?}");
        std::process::exit(1);
    }
    println!(
        "[live] client cell funded on all {} witness node(s).",
        witnesses.len()
    );

    // ── STEP 2 (THE PAYOFF): the fresh client signs its OWN Transfer turn and submits it
    //    via /turns/submit — EXACTLY as payoff_client_turn.rs builds it. ──
    let action = client.make_action(
        actor_cell,
        "attested_client_transfer",
        vec![Effect::Transfer {
            from: actor_cell,
            to: dest_cell,
            amount: transfer_amount,
        }],
        &federation_id,
    );
    let mut turn = client.make_turn(action);
    turn.fee = fee;
    // Attestation-shaped payload riding consensus bound into the turn hash (the same
    // uniform-cross-node carrier as the payoff test; the cryptographic ZkOracleAttestation
    // verify is proven independently by deos-hermes/tests/crown_attested_turn.rs).
    let attestation_blob = {
        let mut v = Vec::new();
        v.extend_from_slice(b"zkoracle-attestation-v1:");
        v.extend_from_slice(client_pubkey.0.as_slice());
        v.extend_from_slice(b":claude-opus-4-8:done");
        v
    };
    turn.memo = Some(format!("att:{}", hex_encode(&attestation_blob)));
    turn.valid_until = Some(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0)
            + 3600,
    );
    let signed = client.sign_turn(&turn);
    let turn_hash_hex = hex_encode(&turn.hash());
    let wire = postcard::to_stdvec(&signed).expect("encode SignedTurn");
    println!("[live] client Transfer turn hash = {turn_hash_hex} (amount {transfer_amount})");

    // ── Submit via /turns/submit (protected route: carries the operator bearer). ──
    let resp = match http_post(
        &node,
        "/turns/submit",
        "application/octet-stream",
        bearer.as_deref(),
        &wire,
    ) {
        Some(r) => r,
        None => {
            eprintln!("[live] FATAL: POST /turns/submit did not reach the node");
            std::process::exit(2);
        }
    };
    println!("[live] /turns/submit response: {resp}");
    if json_field(&resp, "accepted") != Some("true") {
        eprintln!(
            "[live] FATAL: node did not ACCEPT the client turn (optimistic ack). \
             If this is an auth error, set DREGG_NODE_BEARER to the operator's unlock token."
        );
        std::process::exit(1);
    }

    // ── CROSS-NODE / CROSS-MACHINE FINALIZATION WITNESS ──
    let baseline: Vec<u64> = witnesses.iter().map(latest_height).collect();
    let deadline = Instant::now() + Duration::from_secs(timeout_s);
    let mut all_have_dest = false;
    let mut last_dest = vec![(false, 0u64); witnesses.len()];
    let mut last_heights = baseline.clone();
    let mut ticks = 0u32;
    while Instant::now() < deadline {
        std::thread::sleep(Duration::from_secs(2));
        for (i, ep) in witnesses.iter().enumerate() {
            last_dest[i] = cell_balance(ep, &dest_hex);
            last_heights[i] = latest_height(ep);
        }
        ticks += 1;
        if ticks % 5 == 0 {
            println!("[live] …awaiting finality: heights = {last_heights:?}, dest = {last_dest:?}");
        }
        if last_dest.iter().all(|&(f, b)| f && b == transfer_amount) {
            all_have_dest = true;
            break;
        }
    }

    println!("\n[live] ── RESULT ──");
    println!("[live] client signer = {signer_hex}");
    println!("[live] turn hash      = {turn_hash_hex}");
    for (i, ep) in witnesses.iter().enumerate() {
        let (found, bal) = last_dest[i];
        println!(
            "[live]   {:>5} http://{}:{}  latest_height {} -> {}  destination-funded={} (balance {})",
            ep.label,
            ep.host,
            ep.port,
            baseline[i],
            last_heights[i],
            found && bal == transfer_amount,
            bal
        );
    }
    if all_have_dest {
        println!(
            "[live] SUCCESS — the fresh client's attested Transfer finalized on the live \
             federation: destination {dest_hex} funded with {transfer_amount} on ALL {} witness \
             node(s).",
            witnesses.len()
        );
    } else {
        println!(
            "[live] did-not-finalize — the destination was NOT funded on all witness nodes within \
             {timeout_s}s (per node = {last_dest:?})."
        );
        std::process::exit(1);
    }
}
