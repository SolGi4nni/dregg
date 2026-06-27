//! three_node_ordering_rule.rs — the RUNNING-NODE witness that consensus runs at n>1.
//!
//! Klein Stage 5 / HIGH-6: "deployed consensus is n=1 and skips the ordering rule, so the
//! Byzantine-safety theorems are vacuous on the running node." The deployed devnet defaults to
//! `--federation-mode solo` (a committee of one), where `blocklace_sync::poll_finalized_blocks`
//! takes the `participants.len() <= 1` branch and never runs the Cordial-Miners `tau` ordering
//! rule (n=1 trivially finalizes every block). This test stands up THREE REAL `dregg-node`
//! processes in FULL (BFT) mode, with a 3-validator genesis (`threshold = 3`,
//! `supermajority_threshold(3) = 3` — ALL three must ratify a leader), and exercises the REAL
//! multi-party path: real `--consensus blocklace`, the real `dregg_net` QUIC gossip transport,
//! the real `blocklace::ordering::tau` finality rule gated by the verified Lean `dregg_tau_order`
//! export. NO mock consensus, NO shadow — three actual node binaries over the actual wire.
//!
//! It asserts the guarantees that are GENUINELY TRUE on the running node today:
//!
//!   [A] full mode is engaged — every node reports `federation_mode = full` and the multi-party
//!       `tau` branch (participants = 3) is the live finality path, NOT the n=1 solo path. This
//!       is the anti-vacuity tooth: `supermajority_threshold(3) = 3`, so a single node CANNOT
//!       self-finalize a turn — finality REQUIRES cross-node agreement.
//!   [B] cross-node block exchange — a turn block created on node-0 propagates over the real
//!       gossip wire and the shared blocklace DAG grows beyond genesis; at least one node
//!       assembles blocks from >= 2 DISTINCT creators (real wire delivery, not local production).
//!
//! It then PROBES [C]: does a turn finalize through the ordering rule, AGREED across all three
//! nodes (an attested root, `latest_height >= 1`)? Under the node's CURRENT gossip layer this does
//! NOT reliably converge on loopback at small N — the eager/lazy Plumtree mesh over UNIDIRECTIONAL
//! QUIC streams (`net/src/gossip.rs`) delivers blocks asymmetrically, so no node assembles a
//! supermajority of creators' round-blocks and `is_super_ratified` (`blocklace/src/ordering.rs`)
//! never fires. The test MEASURES and REPORTS this precisely (it does not pretend it passes). The
//! consensus RULE is verified (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean`); the open
//! work is the gossip DISSEMINATION leg. See `docs/STAGE5-CONSENSUS-DEVAC.md`.
//!
//! Set `DREGG_TEST_REQUIRE_FINALITY=1` to make [C] a hard assertion (it will FAIL today — that
//! failure is the honest signal the dissemination leg is the remaining work, NOT the ordering
//! rule). This is the dual of the in-process `blocklace/tests/multi_node_convergence.rs`, which
//! proves the SAME `tau` rule finalizes a HAND-BUILT round-synchronous 3-node DAG — here we drive
//! the WHOLE node over the real wire instead.

use std::io::Read;
use std::net::TcpStream;
use std::process::{Child, Command};
use std::time::{Duration, Instant};

/// Where the built `dregg-node` binary lives (Cargo sets this for integration tests).
const NODE_BIN: &str = env!("CARGO_BIN_EXE_dregg-node");

struct NodeProc {
    child: Child,
    http: u16,
    name: &'static str,
}

impl Drop for NodeProc {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Minimal HTTP GET returning the response body as a string (no extra deps — the
/// node serves plain JSON on localhost). Returns None on any connection/parse failure.
fn http_get(port: u16, path: &str) -> Option<String> {
    let mut stream = TcpStream::connect(("127.0.0.1", port)).ok()?;
    stream.set_read_timeout(Some(Duration::from_secs(3))).ok()?;
    stream
        .set_write_timeout(Some(Duration::from_secs(3)))
        .ok()?;
    let req = format!("GET {path} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nConnection: close\r\n\r\n");
    use std::io::Write;
    stream.write_all(req.as_bytes()).ok()?;
    let mut buf = String::new();
    stream.read_to_string(&mut buf).ok()?;
    // Split headers from body at the first blank line.
    let body = buf.split_once("\r\n\r\n")?.1.to_string();
    Some(body)
}

/// Extract a top-level JSON number/string field WITHOUT pulling in serde_json: the
/// `/status` payload is flat and small. Returns the raw token after `"field":`.
fn json_field<'a>(body: &'a str, field: &str) -> Option<&'a str> {
    let key = format!("\"{field}\":");
    let start = body.find(&key)? + key.len();
    let rest = &body[start..];
    let rest = rest.trim_start();
    // value ends at the next ',' or '}' (or '"' close for strings)
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

/// Count DISTINCT block creators a node currently sees in its blocklace — the direct
/// witness of cross-node delivery (1 = sees only itself; >= 2 = received a peer's block
/// over the wire). Parses the `"proposer":"<hex>"` occurrences in `/api/blocklace/blocks`.
fn distinct_proposers(port: u16) -> usize {
    let Some(body) = http_get(port, "/api/blocklace/blocks") else {
        return 0;
    };
    let mut seen = std::collections::HashSet::new();
    let needle = "\"proposer\":\"";
    let mut idx = 0;
    while let Some(rel) = body[idx..].find(needle) {
        let s = idx + rel + needle.len();
        if let Some(end) = body[s..].find('"') {
            seen.insert(body[s..s + end].to_string());
            idx = s + end;
        } else {
            break;
        }
    }
    seen.len()
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

fn run_genesis(tmp: &std::path::Path) {
    let status = Command::new(NODE_BIN)
        .args(["genesis", "--validators", "3", "--output"])
        .arg(tmp)
        .status()
        .expect("spawn `dregg-node genesis`");
    assert!(status.success(), "genesis subcommand failed");
}

#[allow(clippy::too_many_arguments)]
fn launch(
    name: &'static str,
    data_dir: &std::path::Path,
    node_index: usize,
    http: u16,
    gossip: u16,
    peers: &str,
    faucet: bool,
) -> NodeProc {
    let mut cmd = Command::new(NODE_BIN);
    cmd.arg("run")
        .arg("--data-dir")
        .arg(data_dir)
        .args(["--key-file", "node.key"])
        .args(["--node-index", &node_index.to_string()])
        .args(["--federation-size", "3"])
        .args(["--port", &http.to_string()])
        .args(["--gossip-port", &gossip.to_string()])
        .args(["--bind", "127.0.0.1"])
        .args(["--federation-peers", peers])
        .args(["--federation-mode", "full"])
        .args(["--consensus", "blocklace"])
        // measured cadence: heartbeat well above loopback gossip RTT so each round has the
        // best chance to propagate before the next (toward the round-synchronous shape tau finalizes).
        .args(["--idle-heartbeat-ms", "2000"])
        .args(["--block-cadence-ms", "1000"])
        // CONSENSUS is the axis under test; commit via the Rust executor so the finality
        // observable (`latest_height`) is not gated by THE-SWAP's separate Lean-producer
        // differential. The verified Lean FINALITY GATE (`dregg_tau_order`) stays ON regardless.
        .env("DREGG_LEAN_PRODUCER", "0")
        .env("RUST_LOG", "warn")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    if faucet {
        cmd.arg("--enable-faucet");
    }
    let child = cmd.spawn().expect("spawn `dregg-node run`");
    NodeProc { child, http, name }
}

/// The slice: 3 real nodes, full mode, the real ordering rule + real gossip wire.
#[test]
fn three_node_full_mode_runs_the_ordering_rule() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let gen_dir = tmp.path().join("genesis");
    std::fs::create_dir_all(&gen_dir).unwrap();

    // ── 3-validator genesis (committee-derived id, threshold = 3) ──────────────
    run_genesis(&gen_dir);
    let genesis_json = std::fs::read_to_string(gen_dir.join("genesis.json")).unwrap();
    // sanity: threshold 3 (== supermajority_threshold(3)); 3 validators.
    assert!(
        genesis_json.contains("\"threshold\":3") || genesis_json.contains("\"threshold\": 3"),
        "genesis must have threshold 3 (supermajority over 3 validators)"
    );

    // ── per-node data dirs (redb locks the DB exclusively → one dir per node) ──
    for i in 0..3usize {
        let d = tmp.path().join(format!("node-{i}"));
        std::fs::create_dir_all(&d).unwrap();
        std::fs::copy(gen_dir.join("genesis.json"), d.join("genesis.json")).unwrap();
        let _ = std::fs::copy(gen_dir.join(".devnet"), d.join(".devnet"));
        std::fs::copy(gen_dir.join(format!("node-{i}.key")), d.join("node.key")).unwrap();
    }

    // ── launch 3 nodes, fully meshed, FULL mode ────────────────────────────────
    // Distinct, high ports to avoid clashing with a developer's running devnet.
    let (h0, h1, h2) = (8573u16, 8574u16, 8575u16);
    let (g0, g1, g2) = (9583u16, 9584u16, 9585u16);
    let _n0 = launch(
        "node-0",
        &tmp.path().join("node-0"),
        0,
        h0,
        g0,
        &format!("127.0.0.1:{g1},127.0.0.1:{g2}"),
        true,
    );
    std::thread::sleep(Duration::from_secs(1));
    let _n1 = launch(
        "node-1",
        &tmp.path().join("node-1"),
        1,
        h1,
        g1,
        &format!("127.0.0.1:{g0},127.0.0.1:{g2}"),
        false,
    );
    let _n2 = launch(
        "node-2",
        &tmp.path().join("node-2"),
        2,
        h2,
        g2,
        &format!("127.0.0.1:{g0},127.0.0.1:{g1}"),
        false,
    );

    // ── readiness ──────────────────────────────────────────────────────────────
    for (name, p) in [("node-0", h0), ("node-1", h1), ("node-2", h2)] {
        assert!(wait_for_port(p, 40), "{name} never came up on :{p}");
    }

    // ── [A] full mode + multi-party tau path engaged (anti-vacuity) ────────────
    let mut pubkeys = std::collections::HashSet::new();
    for (name, p) in [("node-0", h0), ("node-1", h1), ("node-2", h2)] {
        let mode = status_field(p, "federation_mode").unwrap_or_default();
        assert_eq!(
            mode, "full",
            "[A] {name} must be in FULL mode (not the n=1 solo vacuity); got {mode:?}"
        );
        if let Some(pk) = status_field(p, "public_key") {
            pubkeys.insert(pk);
        }
    }
    assert_eq!(
        pubkeys.len(),
        3,
        "[A] the 3 nodes must have 3 distinct identities (a real committee of three)"
    );
    eprintln!(
        "[A] PASS — 3 nodes in full mode, 3 distinct identities; supermajority(3)=3 ⇒ \
         a single node CANNOT self-finalize. The multi-party tau branch is the live finality path."
    );

    // ── submit a turn on node-0 (real faucet Transfer → real Turn block) ───────
    std::thread::sleep(Duration::from_secs(8)); // let steady rounds build first
    let recipient = "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef";
    let faucet_ok = post_faucet(h0, recipient, 100);
    assert!(faucet_ok, "faucet turn submit on node-0 must succeed");

    // ── [B] cross-node block exchange + [C] finalization probe ─────────────────
    let require_finality = std::env::var("DREGG_TEST_REQUIRE_FINALITY")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false);
    let wait_s: u64 = std::env::var("DREGG_TEST_FINALITY_WAIT_S")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(50);

    let mut grew_beyond_genesis = false;
    let mut best_proposers = 0usize;
    let mut final_ok = false;
    let mut final_heights = (0u64, 0u64, 0u64);
    let deadline = Instant::now() + Duration::from_secs(wait_s);
    while Instant::now() < deadline {
        std::thread::sleep(Duration::from_secs(2));
        for p in [h0, h1, h2] {
            if let Some(dag) = status_field(p, "dag_height").and_then(|s| s.parse::<u64>().ok()) {
                if dag > 1 {
                    grew_beyond_genesis = true;
                }
            }
            best_proposers = best_proposers.max(distinct_proposers(p));
        }
        let h = |p| {
            status_field(p, "latest_height")
                .and_then(|s| s.parse::<u64>().ok())
                .unwrap_or(0)
        };
        final_heights = (h(h0), h(h1), h(h2));
        if final_heights.0 >= 1 && final_heights.1 >= 1 && final_heights.2 >= 1 {
            final_ok = true;
            break;
        }
    }

    // [B] is a hard assertion — cross-node block exchange over the real wire.
    assert!(
        grew_beyond_genesis,
        "[B] the blocklace DAG never grew beyond genesis — no block production"
    );
    assert!(
        best_proposers >= 2,
        "[B] no node ever received a peer's block (gossip delivered nothing cross-node); \
         max distinct creators seen by any node = {best_proposers}"
    );
    eprintln!(
        "[B] PASS — blocks created on one node propagated over the real gossip wire into the \
         shared DAG (max distinct creators seen by a node = {best_proposers})."
    );

    // [C] is the Stage-5 frontier — reported; hard only under DREGG_TEST_REQUIRE_FINALITY=1.
    if final_ok {
        eprintln!(
            "[C] CONVERGED — all 3 nodes reached an attested root (latest_height = {final_heights:?}): \
             the turn committed through the n=3 DAG ordering rule cross-node."
        );
    } else {
        eprintln!(
            "[C] NOT CONVERGED in {wait_s}s (latest_height = {final_heights:?}). The consensus RULE is \
             verified (blocklace::ordering::tau + Lean Distributed/BlocklaceFinality) and cross-node \
             block exchange WORKS ([B] passed), but the node's gossip DISSEMINATION (eager/lazy \
             Plumtree over unidirectional QUIC streams, net/src/gossip.rs) delivers blocks \
             asymmetrically at small N, so no node assembles a supermajority of creators' \
             round-blocks and is_super_ratified (blocklace/src/ordering.rs:263) never fires. \
             See docs/STAGE5-CONSENSUS-DEVAC.md."
        );
        if require_finality {
            panic!(
                "[C] FAILED (DREGG_TEST_REQUIRE_FINALITY=1): no cross-node attested root; \
                 latest_height = {final_heights:?}"
            );
        }
    }
}

/// POST /api/faucet with a tiny hand-rolled HTTP request (no reqwest dep). Returns
/// true iff the response body contains `"success":true`.
fn post_faucet(port: u16, recipient: &str, amount: u64) -> bool {
    let body = format!("{{\"recipient\":\"{recipient}\",\"amount\":{amount}}}");
    let Ok(mut stream) = TcpStream::connect(("127.0.0.1", port)) else {
        return false;
    };
    let _ = stream.set_read_timeout(Some(Duration::from_secs(5)));
    let _ = stream.set_write_timeout(Some(Duration::from_secs(5)));
    let req = format!(
        "POST /api/faucet HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nContent-Type: application/json\r\n\
         Content-Length: {}\r\nConnection: close\r\n\r\n{}",
        body.len(),
        body
    );
    use std::io::Write;
    if stream.write_all(req.as_bytes()).is_err() {
        return false;
    }
    let mut resp = String::new();
    if stream.read_to_string(&mut resp).is_err() {
        return false;
    }
    resp.contains("\"success\":true")
}
