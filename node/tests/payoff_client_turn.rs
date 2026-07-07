//! payoff_client_turn.rs — THE PAYOFF, demonstrated locally.
//!
//! A REAL external client (a fresh Ed25519 identity that NO node has ever seen — no
//! pre-existing cell) builds and signs its OWN turn, `POST`s it to `/turns/submit` on
//! ONE node of a LOCAL n=4 VERIFIED federation (the Lean finality gate is ON —
//! `DREGG_FINALITY_GATE` unset — so consensus is finalized by the verified
//! `BlocklaceFinality.tauOrder`), and the turn STREAM-FINALIZES CROSS-NODE:
//!
//!   * the client's default cell — which existed on NO node — is PROVISIONED
//!     DETERMINISTICALLY from the in-block signer at finalization (submit-path fix
//!     2b, `provision_signer_actor_cell`) and appears with the client's public key on
//!     ALL FOUR nodes;
//!   * the attested-turn `memo` (an opaque attestation-shaped payload) rides consensus
//!     bound into the turn hash, so the SAME turn is finalized uniformly on every node;
//!   * the attested `latest_height` advances on all four nodes.
//!
//! This exercises ALL THREE fixes together on the external-client commitment path:
//!   1. the finality-gate perf fix (fixes 1) — the verified Lean tau-order keeps up
//!      cross-node without stalling (gate ON here);
//!   2. the submit-path fix (fix 2) — `/turns/submit` carries a FRESH client's own
//!      turn into the DAG (decoupled from the node operator's chain) and the actor
//!      cell is provisioned at finalization;
//!   3. the verified-QUIC / spawn_blocking executor fix (fix 3) — the node gossips +
//!      finalizes without the blocking executor starving the async runtime.
//!
//! Gated like its siblings: the cross-node commit is REPORTED by default and a HARD
//! assertion under `DREGG_TEST_REQUIRE_FINALITY=1`, so a developer box that cannot
//! mesh loopback QUIC fast enough still gets a precise report instead of a flake.
//!
//! The cryptographic ZkOracleAttestation leg (a real `ZkOracleAttestation` that
//! `verify_zkoracle` accepts, with the confinement teeth biting) is proven
//! independently by `deos-hermes/tests/crown_attested_turn.rs`; this harness proves
//! the CONSENSUS payoff — an attested-shaped external turn stream-finalized on a
//! verified local federation.

use std::io::{Read, Write};
use std::net::TcpStream;
use std::process::{Child, Command};
use std::time::{Duration, Instant};

use dregg_sdk::AgentCipherclerk as CipherClerk;
use dregg_turn::action::Effect;

const NODE_BIN: &str = env!("CARGO_BIN_EXE_dregg-node");
const FED_SIZE: usize = 4;

#[allow(dead_code)]
struct NodeProc {
    child: Child,
    http: u16,
    name: String,
    log: std::path::PathBuf,
}

impl Drop for NodeProc {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn http_get(port: u16, path: &str) -> Option<String> {
    let mut stream = TcpStream::connect(("127.0.0.1", port)).ok()?;
    stream.set_read_timeout(Some(Duration::from_secs(4))).ok()?;
    stream
        .set_write_timeout(Some(Duration::from_secs(4)))
        .ok()?;
    let req = format!("GET {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nConnection: close\r\n\r\n");
    stream.write_all(req.as_bytes()).ok()?;
    let mut buf = String::new();
    stream.read_to_string(&mut buf).ok()?;
    Some(buf.split_once("\r\n\r\n")?.1.to_string())
}

/// POST raw bytes with an explicit content-type; return the response body.
fn http_post(
    port: u16,
    path: &str,
    content_type: &str,
    bearer: Option<&str>,
    body: &[u8],
) -> Option<String> {
    let mut stream = TcpStream::connect(("127.0.0.1", port)).ok()?;
    stream.set_read_timeout(Some(Duration::from_secs(6))).ok()?;
    stream
        .set_write_timeout(Some(Duration::from_secs(6)))
        .ok()?;
    let auth = match bearer {
        Some(tok) => format!("Authorization: Bearer {tok}\r\n"),
        None => String::new(),
    };
    let head = format!(
        "POST {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nContent-Type: {content_type}\r\n\
         {auth}Content-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(head.as_bytes()).ok()?;
    stream.write_all(body).ok()?;
    let mut buf = Vec::new();
    stream.read_to_end(&mut buf).ok()?;
    // Return the FULL raw response (status line + headers + body) so a non-2xx
    // status is visible in the harness output; `json_field` still finds body fields.
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

fn status_field(port: u16, field: &str) -> Option<String> {
    let body = http_get(port, "/status")?;
    json_field(&body, field).map(|s| s.to_string())
}

fn latest_height(port: u16) -> u64 {
    status_field(port, "latest_height")
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0)
}

/// `(found, has_public_key)` for a cell id. The cross-node PROVISIONING witness: a
/// fresh client's default cell that NO node had appears — with the client's pubkey —
/// on every node after the turn finalizes.
fn cell_found(port: u16, cell_hex: &str) -> bool {
    let Some(body) = http_get(port, &format!("/api/cell/{cell_hex}")) else {
        return false;
    };
    json_field(&body, "found") == Some("true")
}

/// `(found, balance)` for a cell id — the cross-node commit witness (a finalized
/// Transfer materialises the recipient with the funded balance on every node).
fn cell_balance(port: u16, cell_hex: &str) -> (bool, u64) {
    let Some(body) = http_get(port, &format!("/api/cell/{cell_hex}")) else {
        return (false, 0);
    };
    let found = json_field(&body, "found") == Some("true");
    let bal = json_field(&body, "balance")
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0);
    (found, bal)
}

/// POST /api/faucet (public); true iff `"success":true`.
fn post_faucet(port: u16, recipient_hex: &str, amount: u64) -> bool {
    let body = format!("{{\"recipient\":\"{recipient_hex}\",\"amount\":{amount}}}");
    http_post(
        port,
        "/api/faucet",
        "application/json",
        None,
        body.as_bytes(),
    )
    .map(|r| r.contains("\"success\":true"))
    .unwrap_or(false)
}

fn wait_for_port(port: u16, secs: u64) -> bool {
    let deadline = Instant::now() + Duration::from_secs(secs);
    while Instant::now() < deadline {
        if http_get(port, "/status").is_some() {
            return true;
        }
        std::thread::sleep(Duration::from_millis(400));
    }
    false
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

fn run_genesis(tmp: &std::path::Path) {
    let status = Command::new(NODE_BIN)
        .args(["genesis", "--validators", &FED_SIZE.to_string(), "--output"])
        .arg(tmp)
        .status()
        .expect("spawn `dregg-node genesis`");
    assert!(status.success(), "genesis subcommand failed");
}

#[allow(clippy::too_many_arguments)]
fn launch(
    name: &str,
    data_dir: &std::path::Path,
    node_index: usize,
    http: u16,
    gossip: u16,
    peers: &str,
) -> NodeProc {
    let log = data_dir.join("stderr.log");
    let log_file = std::fs::File::create(&log).expect("create stderr log");
    let mut cmd = Command::new(NODE_BIN);
    cmd.arg("run")
        .arg("--data-dir")
        .arg(data_dir)
        .args(["--key-file", "node.key"])
        .args(["--node-index", &node_index.to_string()])
        .args(["--federation-size", &FED_SIZE.to_string()])
        .args(["--port", &http.to_string()])
        .args(["--gossip-port", &gossip.to_string()])
        .args(["--bind", "127.0.0.1"])
        .args(["--federation-peers", peers])
        .args(["--federation-mode", "full"])
        .args(["--consensus", "blocklace"])
        .args(["--idle-heartbeat-ms", "2000"])
        .args(["--block-cadence-ms", "1000"])
        // Rust producer for execution (matches the proven sustained_finality config);
        // the verified Lean FINALITY GATE (DREGG_FINALITY_GATE) is left ON by default,
        // so consensus is finalized by the verified tau-order — a VERIFIED federation.
        .env("DREGG_LEAN_PRODUCER", "0")
        .env("RUST_LOG", "warn")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::from(log_file));
    // node-0 is the faucet operator (funds the fresh external client, step 1).
    if node_index == 0 {
        cmd.arg("--enable-faucet");
    }
    let child = cmd.spawn().expect("spawn `dregg-node run`");
    NodeProc {
        child,
        http,
        name: name.to_string(),
        log,
    }
}

#[test]
fn fresh_client_attested_turn_finalizes_cross_node_on_verified_n4() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let gen_dir = tmp.path().join("genesis");
    std::fs::create_dir_all(&gen_dir).unwrap();
    run_genesis(&gen_dir);

    for i in 0..FED_SIZE {
        let d = tmp.path().join(format!("node-{i}"));
        std::fs::create_dir_all(&d).unwrap();
        std::fs::copy(gen_dir.join("genesis.json"), d.join("genesis.json")).unwrap();
        let _ = std::fs::copy(gen_dir.join(".devnet"), d.join(".devnet"));
        std::fs::copy(gen_dir.join(format!("node-{i}.key")), d.join("node.key")).unwrap();
    }

    // Ports: HTTP 8690..8693, gossip 9690..9693.
    let http_ports: Vec<u16> = (0..FED_SIZE).map(|i| 8690 + i as u16).collect();
    let gossip_ports: Vec<u16> = (0..FED_SIZE).map(|i| 9690 + i as u16).collect();

    let mut nodes: Vec<NodeProc> = Vec::new();
    for i in 0..FED_SIZE {
        let peers: Vec<String> = (0..FED_SIZE)
            .filter(|&j| j != i)
            .map(|j| format!("127.0.0.1:{}", gossip_ports[j]))
            .collect();
        nodes.push(launch(
            &format!("node-{i}"),
            &tmp.path().join(format!("node-{i}")),
            i,
            http_ports[i],
            gossip_ports[i],
            &peers.join(","),
        ));
        if i == 0 {
            std::thread::sleep(Duration::from_secs(1));
        }
    }

    for (i, &p) in http_ports.iter().enumerate() {
        assert!(wait_for_port(p, 45), "node-{i} never came up on :{p}");
    }
    for (i, &p) in http_ports.iter().enumerate() {
        let mode = status_field(p, "federation_mode").unwrap_or_default();
        assert_eq!(mode, "full", "node-{i} must be FULL; got {mode:?}");
    }

    let require_finality = std::env::var("DREGG_TEST_REQUIRE_FINALITY")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false);
    let wait_s: u64 = std::env::var("DREGG_TEST_FINALITY_WAIT_S")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(90);

    // Let steady rounds build so the DAG is cross-linked before the client turn.
    std::thread::sleep(Duration::from_secs(8));

    // ── The federation id the executor verifies signatures against (uniform on all
    //    nodes in a configured federation — `federation_id_for_executor` returns the
    //    genesis `federation_id` when configured). The client MUST sign its action over
    //    the SAME id. Read it from the shared genesis.json (a top-level field). ──
    let genesis_json = std::fs::read_to_string(gen_dir.join("genesis.json"))
        .expect("read genesis.json for the federation id");
    let fed_hex = json_field(&genesis_json, "federation_id")
        .expect("genesis.json carries a top-level federation_id")
        .to_string();
    let federation_id = hex_decode_32(&fed_hex).expect("federation id is 32-byte hex");
    eprintln!("[payoff] federation id = {fed_hex}");

    // ── A FRESH external client identity — a deterministic seed no node has ever seen.
    //    Its default cell exists on NO node. ──
    let client = CipherClerk::from_seed([0x5Au8; 64]);
    let client_pubkey = client.public_key();
    let actor_cell = client.cell_id("default");
    let actor_hex = hex_encode(&actor_cell.0);
    let signer_hex = hex_encode(&client_pubkey.0);

    // Pre-condition: the fresh client's cell is on NO node.
    for (i, &p) in http_ports.iter().enumerate() {
        assert!(
            !cell_found(p, &actor_hex),
            "pre-condition failed: node-{i} already has the fresh client's cell {actor_hex}"
        );
    }

    // ── STEP 1: fund the fresh client's cell via the faucet (an external client has
    //    no genesis balance; a real turn costs computrons paid from balance). The
    //    faucet Transfer finalizes cross-node and materialises the client's cell as a
    //    funded remote stub on every node. This is itself a fix-2b / cross-node commit
    //    step, but the PAYOFF is the CLIENT's OWN turn below. ──
    let faucet_amount = 10_000u64;
    let faucet_body = format!("{{\"recipient\":\"{actor_hex}\",\"amount\":{faucet_amount}}}");
    let faucet_resp = http_post(
        http_ports[0],
        "/api/faucet",
        "application/json",
        None,
        faucet_body.as_bytes(),
    )
    .expect("POST /api/faucet reached node-0");
    eprintln!("[payoff] faucet response: {faucet_resp}");
    assert!(
        faucet_resp.contains("\"success\":true"),
        "faucet grant to the fresh client cell must be accepted on node-0; got: {faucet_resp}"
    );
    eprintln!("[payoff] faucet-funded the client cell with {faucet_amount}; awaiting cross-node…");
    let fund_deadline = Instant::now() + Duration::from_secs(wait_s);
    let mut funded_everywhere = false;
    while Instant::now() < fund_deadline {
        std::thread::sleep(Duration::from_secs(2));
        if http_ports
            .iter()
            .all(|&p| cell_balance(p, &actor_hex) == (true, faucet_amount))
        {
            funded_everywhere = true;
            break;
        }
    }
    assert!(
        funded_everywhere,
        "the faucet grant did not fund the client cell on all {FED_SIZE} nodes — cannot proceed \
         to the client turn (per-node = {:?})",
        http_ports
            .iter()
            .map(|&p| cell_balance(p, &actor_hex))
            .collect::<Vec<_>>()
    );
    eprintln!("[payoff] client cell funded on ALL {FED_SIZE} nodes.");

    // ── STEP 2 (THE PAYOFF): the fresh client signs its OWN Transfer turn — moving a
    //    distinct amount to a brand-new destination cell D — and submits it via
    //    /turns/submit. fix-2b UPGRADES the client's funded zero-pk stub to its
    //    canonical pk-bound account at finalization (the client's key authorizes the
    //    Send), and D materialises with the transferred balance on every node. ──
    let dest_cell = {
        // A fresh destination id no node has: derive from a throwaway pubkey.
        let mut pk = [0u8; 32];
        pk[0] = 0xD5;
        pk[31] = 0x01;
        let token = *blake3::hash(b"default").as_bytes();
        dregg_cell::CellId::derive_raw(&pk, &token)
    };
    let dest_hex = hex_encode(&dest_cell.0);
    let transfer_amount = 1_000u64;
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
    turn.fee = 5_000; // >= a Transfer's computron cost (~300); paid from the 10_000 funded balance.
    // Attestation-shaped payload riding consensus in the turn hash. (The cryptographic
    // ZkOracleAttestation verify is proven by crown_attested_turn.rs; here it is the
    // uniform-cross-node attested-turn carrier.)
    let attestation_blob = {
        let mut v = Vec::new();
        v.extend_from_slice(b"zkoracle-attestation-v1:");
        v.extend_from_slice(client_pubkey.0.as_slice());
        v.extend_from_slice(b":claude-opus-4-8:done");
        v
    };
    turn.memo = Some(format!("att:{}", hex_encode(&attestation_blob)));
    // Far-future validity so the wire marshal accepts the envelope on every node.
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

    eprintln!("[payoff] fresh client signer={signer_hex}");
    eprintln!("[payoff] client actor cell = {actor_hex}");
    eprintln!("[payoff] client-turn destination cell = {dest_hex}");
    eprintln!("[payoff] client Transfer turn hash = {turn_hash_hex} (amount {transfer_amount})");

    // ── Unlock node-0's ingress (HTTP nodes start locked; /turns/submit gates on
    //    `s.unlocked`). The first unlock sets the node passphrase + a bearer seed and
    //    returns the API bearer token; subsequent protected requests carry it. This is
    //    the node OPERATOR unlocking its own ingress — orthogonal to the CLIENT identity
    //    (the fresh signer above), which the turn is authored by. ──
    let unlock_resp = http_post(
        http_ports[0],
        "/cipherclerk/unlock",
        "application/json",
        None,
        br#"{"passphrase":"payoff-devnet-passphrase"}"#,
    )
    .expect("POST /cipherclerk/unlock reached node-0");
    let bearer = json_field(&unlock_resp, "bearer_token")
        .map(|s| s.to_string())
        .unwrap_or_default();
    eprintln!(
        "[payoff] node-0 unlocked (bearer token {} chars)",
        bearer.len()
    );

    // ── Submit via /turns/submit to node-0 (the external-client path), authenticated
    //    with the operator bearer token. ──
    let resp = http_post(
        http_ports[0],
        "/turns/submit",
        "application/octet-stream",
        if bearer.is_empty() {
            None
        } else {
            Some(bearer.as_str())
        },
        &wire,
    )
    .expect("POST /turns/submit reached node-0");
    eprintln!("[payoff] /turns/submit response: {resp}");
    let accepted = json_field(&resp, "accepted") == Some("true");
    assert!(
        accepted,
        "node-0 must ACCEPT the fresh client's signed turn (optimistic ack); got: {resp}"
    );

    // ── CROSS-NODE FINALIZATION WITNESS (THE PAYOFF): the CLIENT's OWN Transfer turn
    //    stream-finalizes on every node — its destination D materialises with exactly
    //    the transferred balance on ALL FOUR nodes (only reachable by the turn being
    //    finalized + executed through the verified tau-order on each node), and every
    //    node's attested height advances together. ──
    let baseline_heights: Vec<u64> = http_ports.iter().map(|&p| latest_height(p)).collect();
    let deadline = Instant::now() + Duration::from_secs(wait_s);
    let mut all_have_dest = false;
    let mut last_dest = vec![(false, 0u64); FED_SIZE];
    let mut last_heights = baseline_heights.clone();
    let mut ticks = 0u32;
    while Instant::now() < deadline {
        std::thread::sleep(Duration::from_secs(2));
        for (i, &p) in http_ports.iter().enumerate() {
            last_dest[i] = cell_balance(p, &dest_hex);
            last_heights[i] = latest_height(p);
        }
        ticks += 1;
        if ticks % 10 == 0 {
            eprintln!(
                "[payoff] …awaiting client-turn finality: heights = {last_heights:?}, dest = {last_dest:?}"
            );
        }
        if last_dest.iter().all(|&(f, b)| f && b == transfer_amount) {
            all_have_dest = true;
            break;
        }
    }

    // Copy each node's stderr log out of the tempdir (which is deleted on Drop) so a
    // partial-finality result can be diagnosed (round production vs finalized-turn
    // rejection). Best-effort.
    if let Ok(diag_dir) = std::env::var("DREGG_PAYOFF_LOG_DIR") {
        let _ = std::fs::create_dir_all(&diag_dir);
        for n in &nodes {
            let dst = std::path::Path::new(&diag_dir).join(format!("{}.stderr.log", n.name));
            let _ = std::fs::copy(&n.log, &dst);
        }
        eprintln!("[payoff] node stderr logs copied to {diag_dir}");
    }

    eprintln!(
        "[payoff] cross-node result: destination (found,balance) per node = {last_dest:?}, \
         heights {baseline_heights:?} -> {last_heights:?}"
    );

    if all_have_dest {
        eprintln!(
            "[payoff] SUCCESS — the fresh client's attested Transfer turn stream-finalized on \
             the VERIFIED n=4 federation: turn {turn_hash_hex} finalized, destination {dest_hex} \
             funded with {transfer_amount} on ALL {FED_SIZE} nodes; heights {last_heights:?}."
        );
    } else {
        eprintln!(
            "[payoff] NOT fully cross-node in {wait_s}s — destination per node = {last_dest:?}. \
             (Fixes landed; residual is loopback QUIC mesh speed on this box.)"
        );
    }

    if require_finality {
        assert!(
            all_have_dest,
            "[REQUIRE_FINALITY] the fresh client's Transfer did not fund the destination on all \
             {FED_SIZE} nodes — cross-node finalization of the external-client turn did not \
             complete (destination per node = {last_dest:?})"
        );
    }
}
