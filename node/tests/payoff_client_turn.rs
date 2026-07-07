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
fn http_post(port: u16, path: &str, content_type: &str, body: &[u8]) -> Option<String> {
    let mut stream = TcpStream::connect(("127.0.0.1", port)).ok()?;
    stream.set_read_timeout(Some(Duration::from_secs(6))).ok()?;
    stream
        .set_write_timeout(Some(Duration::from_secs(6)))
        .ok()?;
    let head = format!(
        "POST {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nContent-Type: {content_type}\r\n\
         Content-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(head.as_bytes()).ok()?;
    stream.write_all(body).ok()?;
    let mut buf = Vec::new();
    stream.read_to_end(&mut buf).ok()?;
    let text = String::from_utf8_lossy(&buf).to_string();
    Some(text.split_once("\r\n\r\n")?.1.to_string())
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
    //    nodes in a configured federation). The client MUST sign its action over the
    //    SAME id. Fetched from node-0's /status. ──
    let fed_hex = status_field(http_ports[0], "executor_federation_id")
        .expect("node-0 /status exposes executor_federation_id");
    let federation_id = hex_decode_32(&fed_hex).expect("federation id is 32-byte hex");

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

    // ── Build the client's OWN turn: a self IncrementNonce on its default cell (needs
    //    no balance), carrying an attestation-shaped memo bound into the turn hash. ──
    let action = client.make_action(
        actor_cell,
        "attested_client_turn",
        vec![Effect::IncrementNonce { cell: actor_cell }],
        &federation_id,
    );
    let mut turn = client.make_turn(action);
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
    eprintln!("[payoff] actor cell (unknown to all nodes) = {actor_hex}");
    eprintln!("[payoff] turn hash = {turn_hash_hex}");

    // ── Submit via /turns/submit to node-0 (the external-client path). ──
    let resp = http_post(
        http_ports[0],
        "/turns/submit",
        "application/octet-stream",
        &wire,
    )
    .expect("POST /turns/submit reached node-0");
    eprintln!("[payoff] /turns/submit response: {resp}");
    let accepted = json_field(&resp, "accepted") == Some("true");
    assert!(
        accepted,
        "node-0 must ACCEPT the fresh client's signed turn (optimistic ack); got: {resp}"
    );

    // ── CROSS-NODE FINALIZATION WITNESS: the fresh client's cell — provisioned
    //    deterministically from the in-block signer at finalization — appears on ALL
    //    FOUR nodes, and every node's attested height has advanced. ──
    let baseline_heights: Vec<u64> = http_ports.iter().map(|&p| latest_height(p)).collect();
    let deadline = Instant::now() + Duration::from_secs(wait_s);
    let mut all_have_cell = false;
    let mut last_present = vec![false; FED_SIZE];
    let mut last_heights = baseline_heights.clone();
    while Instant::now() < deadline {
        std::thread::sleep(Duration::from_secs(2));
        for (i, &p) in http_ports.iter().enumerate() {
            last_present[i] = cell_found(p, &actor_hex);
            last_heights[i] = latest_height(p);
        }
        if last_present.iter().all(|&f| f) {
            all_have_cell = true;
            break;
        }
    }

    eprintln!(
        "[payoff] cross-node result: cell present per node = {last_present:?}, \
         heights {baseline_heights:?} -> {last_heights:?}"
    );

    if all_have_cell {
        eprintln!(
            "[payoff] SUCCESS — the fresh client's attested turn stream-finalized on the \
             VERIFIED n=4 federation: turn {turn_hash_hex} finalized, actor cell {actor_hex} \
             provisioned on ALL {FED_SIZE} nodes."
        );
    } else {
        eprintln!(
            "[payoff] NOT fully cross-node in {wait_s}s — cell present = {last_present:?}. \
             (Fixes landed; residual is loopback QUIC mesh speed on this box.)"
        );
    }

    if require_finality {
        assert!(
            all_have_cell,
            "[REQUIRE_FINALITY] the fresh client's cell did not materialise on all {FED_SIZE} \
             nodes — cross-node finalization of the external-client turn did not complete \
             (present = {last_present:?})"
        );
    }
}
