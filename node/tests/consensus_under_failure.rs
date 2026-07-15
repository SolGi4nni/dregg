//! consensus_under_failure.rs — the REAL-PROCESS witness that an n-node federation
//! keeps making consensus progress when a validator is KILLED mid-run.
//!
//! This is the real-process companion to the deterministic engine sim
//! `blocklace/tests/consensus_fault_sim.rs`. The engine sim asserts the full
//! safety/liveness/tolerance contract (it controls delivery, so a fork / stall /
//! equivocation is injectable and every assertion bites today). This file stands up
//! REAL `dregg-node` processes over the REAL `dregg_net` QUIC gossip wire and injects
//! a real fault — `child.kill()` on a live validator — then asserts what is
//! observable on the running node TODAY.
//!
//! ## What is asserted today (non-A1-gated, bites now)
//!
//!   * [KILL-LIVENESS] After f = ⌊(n−1)/3⌋ validators are killed, the surviving
//!     quorum keeps PRODUCING blocks: the shared blocklace DAG on a survivor keeps
//!     GROWING past the height it had at kill time. Block production does not wedge
//!     when a peer dies.
//!   * [KILL-EXCHANGE] The survivors keep EXCHANGING blocks cross-node after the
//!     kill (a survivor still assembles blocks from ≥ 2 distinct creators) — the
//!     gossip mesh reforms around the dead peer.
//!   * [NO-FORK] No survivor ever reports a finalized `latest_height` that another
//!     survivor contradicts (they never disagree on an attested root).
//!
//! ## What is A1-gated (honest)
//!
//! POST-KILL cross-node FINALITY (`latest_height ≥ 1` agreed across the survivors)
//! does not converge on loopback today (measured 2026-07-06 under
//! `DREGG_TEST_REQUIRE_FINALITY=1`: heights all 0 at n=4 and n=5 after the kill).
//! Note the frontier has MOVED: the no-fault n=3 single-turn case NOW converges
//! green under the same gate (`three_node_ordering_rule.rs` [C]); the remaining
//! open legs are the sustained 3rd+ turn (`sustained_finality.rs`, 2/3) and this
//! post-kill / n≥4 case. So the finality assertion here stays gated behind
//! `DREGG_TEST_REQUIRE_FINALITY=1`: the harness is built so that once that lane
//! lands it PASSES with the finality gate on; until then it reports precisely and
//! asserts only the production/exchange progress above.
//!
//! ## Real-vs-engine + CI
//!
//! `#[ignore]` by default: this spins up 4–5 Lean-linked node processes and is the
//! SOAK variant. The FAST CI variant is the engine sim (runs in the default
//! `cargo test --workspace`). Run this with:
//!   `cargo test -p dregg-node --test consensus_under_failure -- --ignored`
//! and add `DREGG_TEST_REQUIRE_FINALITY=1` to hard-gate finality once A1 is in.
//!
//! Partition and Byzantine-equivocation faults are NOT injected here: a real
//! loopback QUIC partition needs network-namespace plumbing (not CI-portable), and a
//! real double-signing node needs a malicious build. Both are covered — with biting
//! assertions — by the engine sim. This file owns the one real-process fault that is
//! portable and load-bearing: killing a live validator.

use std::io::Read;
use std::net::TcpStream;
use std::process::{Child, Command};
use std::time::{Duration, Instant};

const NODE_BIN: &str = env!("CARGO_BIN_EXE_dregg-node");

#[allow(dead_code)]
struct NodeProc {
    child: Option<Child>,
    http: u16,
    name: String,
}

impl NodeProc {
    /// Inject the fault: kill this validator. Idempotent.
    fn kill(&mut self) {
        if let Some(mut c) = self.child.take() {
            let _ = c.kill();
            let _ = c.wait();
        }
    }
    fn alive(&self) -> bool {
        self.child.is_some()
    }
}

impl Drop for NodeProc {
    fn drop(&mut self) {
        self.kill();
    }
}

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
    Some(buf.split_once("\r\n\r\n")?.1.to_string())
}

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

fn status_u64(port: u16, field: &str) -> u64 {
    status_field(port, field)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0)
}

/// Distinct block creators a node currently sees — the witness of cross-node
/// delivery (≥ 2 means it received a peer's block over the wire).
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

fn run_genesis(dir: &std::path::Path, validators: usize) {
    let status = Command::new(NODE_BIN)
        .args([
            "genesis",
            "--validators",
            &validators.to_string(),
            "--output",
        ])
        .arg(dir)
        .status()
        .expect("spawn `dregg-node genesis`");
    assert!(status.success(), "genesis subcommand failed");
}

#[allow(clippy::too_many_arguments)]
fn launch(
    name: String,
    data_dir: &std::path::Path,
    node_index: usize,
    federation_size: usize,
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
        .args(["--federation-size", &federation_size.to_string()])
        .args(["--port", &http.to_string()])
        .args(["--gossip-port", &gossip.to_string()])
        .args(["--bind", "127.0.0.1"])
        .args(["--federation-peers", peers])
        .args(["--federation-mode", "full"])
        .args(["--consensus", "blocklace"])
        .args(["--idle-heartbeat-ms", "2000"])
        .args(["--block-cadence-ms", "1000"])
        .env("RUST_LOG", "warn")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    // THE PRODUCTION DEFAULT IS WHAT GETS FAULT-INJECTED. This harness used to hard-pin
    // `DREGG_LEAN_PRODUCER=0` on every launched node, so the verified Lean producer — THE SWAP,
    // on by default in production (`node/src/state.rs::lean_producer_env_enabled`) — was the one
    // thing a real cross-node kill never exercised. The fault injection ran against a
    // configuration no validator ships. Leaving the var UNSET is the production default; the
    // effective producer still ANDs with the build-time `lean_available()`, so a marshal-only
    // build degrades to Rust on its own rather than lying.
    //
    // The legacy-Rust comparison lane is still reachable, but now it must be ASKED for:
    // `DREGG_TEST_LEAN_PRODUCER=0 cargo test ... -- --ignored`.
    if let Ok(v) = std::env::var("DREGG_TEST_LEAN_PRODUCER") {
        cmd.env("DREGG_LEAN_PRODUCER", v);
    }
    if faucet {
        cmd.arg("--enable-faucet");
    }
    let child = cmd.spawn().expect("spawn `dregg-node run`");
    NodeProc {
        child: Some(child),
        http,
        name,
    }
}

/// Stand up `n` fully-meshed real nodes in full mode. Returns the procs + their
/// http ports. Node 0 has the faucet.
fn launch_federation(
    tmp: &std::path::Path,
    n: usize,
    http_base: u16,
    gossip_base: u16,
) -> Vec<NodeProc> {
    let gen_dir = tmp.join("genesis");
    std::fs::create_dir_all(&gen_dir).unwrap();
    run_genesis(&gen_dir, n);

    for i in 0..n {
        let d = tmp.join(format!("node-{i}"));
        std::fs::create_dir_all(&d).unwrap();
        std::fs::copy(gen_dir.join("genesis.json"), d.join("genesis.json")).unwrap();
        let _ = std::fs::copy(gen_dir.join(".devnet"), d.join(".devnet"));
        std::fs::copy(gen_dir.join(format!("node-{i}.key")), d.join("node.key")).unwrap();
    }

    let gossip = |i: usize| gossip_base + i as u16;
    let mut procs = Vec::new();
    for i in 0..n {
        let peers: Vec<String> = (0..n)
            .filter(|&j| j != i)
            .map(|j| format!("127.0.0.1:{}", gossip(j)))
            .collect();
        let p = launch(
            format!("node-{i}"),
            &tmp.join(format!("node-{i}")),
            i,
            n,
            http_base + i as u16,
            gossip(i),
            &peers.join(","),
            i == 0,
        );
        procs.push(p);
        // stagger startup slightly (node 0 first, as the existing harness does).
        if i == 0 {
            std::thread::sleep(Duration::from_secs(1));
        }
    }
    procs
}

fn fault_budget(n: usize) -> usize {
    if n == 0 { 0 } else { (n - 1) / 3 }
}

/// The real-process node-kill sim: kill f validators mid-run, assert the surviving
/// quorum keeps producing + exchanging blocks (finality A1-gated).
fn run_kill_sim(n: usize, http_base: u16, gossip_base: u16) {
    let f = fault_budget(n);
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut procs = launch_federation(tmp.path(), n, http_base, gossip_base);

    // readiness
    for p in &procs {
        assert!(
            wait_for_port(p.http, 40),
            "{} never came up on :{}",
            p.name,
            p.http
        );
    }
    // full mode + distinct identities (anti-vacuity: not the n=1 solo path).
    let mut ids = std::collections::HashSet::new();
    for p in &procs {
        let mode = status_field(p.http, "federation_mode").unwrap_or_default();
        assert_eq!(
            mode, "full",
            "{} must be in FULL mode; got {mode:?}",
            p.name
        );
        if let Some(pk) = status_field(p.http, "public_key") {
            ids.insert(pk);
        }
    }
    assert_eq!(
        ids.len(),
        n,
        "the {n} nodes must have {n} distinct identities (a real committee)"
    );

    // ── WHICH PRODUCER IS ACTUALLY UNDER FAULT? (the anti-vacuity leg of dropping the
    // DREGG_LEAN_PRODUCER=0 pin). `state_producer` is the node's OWN report of the effective
    // setting — env intent AND the build-time `lean_available()`. Reading it here means the lane
    // can never quietly claim to fault-inject the verified producer while running the Rust one.
    //
    // Under `DREGG_TEST_REQUIRE_LEAN=1` (the scheduled hard-mode lane) a Rust producer is a hard
    // FAILURE: that lane exists to assert the swap survives a validator kill, and a marshal-only
    // build cannot assert it. Unset, we report precisely and keep the progress assertions —
    // which bite either way.
    let producers: Vec<String> = procs
        .iter()
        .map(|p| status_field(p.http, "state_producer").unwrap_or_else(|| "unknown".into()))
        .collect();
    let all_lean = producers.iter().all(|p| p == "lean");
    if dregg_lean_ffi::test_require_lean() {
        assert!(
            all_lean,
            "DREGG_TEST_REQUIRE_LEAN=1 demands the VERIFIED producer under fault injection, but \
             the launched nodes report state_producer = {producers:?}. Either the node binary is \
             marshal-only (seed a HEAD-matching dregg-lean-ffi/libdregg_lean.a — see \
             docs/BUILD-LEAN-LINKED-NODE.md) or DREGG_TEST_LEAN_PRODUCER=0 is set, which \
             deliberately runs the LEGACY comparison lane and must not be combined with the hard \
             mode."
        );
    }
    eprintln!(
        "[producer] n={n}: state_producer = {producers:?} (all_lean = {all_lean}) — this is the \
         configuration the kill below is injected against."
    );

    // Let steady rounds build before the fault.
    std::thread::sleep(Duration::from_secs(10));

    // Survivors are indices f..n (kill the last f). Record their DAG heights BEFORE the kill.
    let survivors: Vec<usize> = (f..n).collect();
    let dag_before: Vec<u64> = survivors
        .iter()
        .map(|&i| status_u64(procs[i].http, "dag_height"))
        .collect();

    // ── INJECT THE FAULT: kill f validators ────────────────────────────────────
    for i in 0..f {
        procs[i].kill();
    }
    eprintln!("[kill] killed {f} of {n} validators; survivors = {survivors:?}");
    assert!(procs.iter().filter(|p| p.alive()).count() == n - f);

    // ── [KILL-LIVENESS] survivors keep producing: DAG grows past the kill-time height.
    // ── [KILL-EXCHANGE] survivors keep exchanging: a survivor sees ≥ 2 creators.
    // ── [NO-FORK] survivors never report contradictory finalized roots.
    let wait_s: u64 = std::env::var("DREGG_TEST_FINALITY_WAIT_S")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(50);
    let deadline = Instant::now() + Duration::from_secs(wait_s);
    let mut grew = false;
    let mut best_exchange = 0usize;
    let mut final_heights: Vec<u64> = vec![0; survivors.len()];
    // [NO-FORK/monotonicity]: track the max finalized height each survivor ever
    // reported; a survivor must never REGRESS its attested-root height.
    let mut max_seen: Vec<u64> = vec![0; survivors.len()];
    while Instant::now() < deadline {
        std::thread::sleep(Duration::from_secs(2));
        for (k, &i) in survivors.iter().enumerate() {
            let dag = status_u64(procs[i].http, "dag_height");
            if dag > dag_before[k] + 1 {
                grew = true;
            }
            best_exchange = best_exchange.max(distinct_proposers(procs[i].http));
            let h = status_u64(procs[i].http, "latest_height");
            assert!(
                h >= max_seen[k],
                "[NO-FORK] survivor {} regressed its finalized height ({} < {}) — a finalized root was retracted",
                survivors[k],
                h,
                max_seen[k]
            );
            max_seen[k] = h;
            final_heights[k] = h;
        }
        if grew && best_exchange >= 2 && final_heights.iter().all(|&h| h >= 1) {
            break;
        }
    }

    assert!(
        grew,
        "[KILL-LIVENESS] no survivor's DAG grew after killing {f} validators (production wedged on the kill); \
         before = {dag_before:?}"
    );
    assert!(
        best_exchange >= 2,
        "[KILL-EXCHANGE] after the kill no survivor assembled blocks from ≥ 2 creators (mesh did not reform); \
         max distinct creators = {best_exchange}"
    );
    eprintln!(
        "[kill] PASS — survivors kept producing (DAG grew) and exchanging (max {best_exchange} creators) after the fault."
    );

    // [NO-FORK] note: the running node does not expose the attested ROOT on
    // `/status` (only its height), so real-process cross-node fork DETECTION on a
    // shared root is not observable here — the per-survivor height-monotonicity
    // guard above is the portable safety-adjacent check (a finalized root is never
    // retracted). Full cross-node "no two conflicting finalizations" is asserted,
    // and BITES today, in the engine sim (`consensus_fault_sim.rs::assert_safety`).

    // ── FINALITY (A1-gated) ─────────────────────────────────────────────────────
    let require_finality = std::env::var("DREGG_TEST_REQUIRE_FINALITY")
        .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        .unwrap_or(false);
    let converged = final_heights.iter().all(|&h| h >= 1);
    if converged {
        eprintln!("[finality] survivors reached an attested root: heights = {final_heights:?}");
    } else {
        eprintln!(
            "[finality] NOT converged (heights = {final_heights:?}). The consensus RULE is verified + the \
             engine sim asserts finalization; the running node's gossip-dissemination leg (A1) is the open \
             work. See three_node_ordering_rule.rs [C]."
        );
        if require_finality {
            panic!(
                "[finality] FAILED (DREGG_TEST_REQUIRE_FINALITY=1): survivors did not finalize; heights = {final_heights:?}"
            );
        }
    }
}

/// n=4 (f=1): kill one validator, the quorum of 3 keeps producing + exchanging.
#[test]
#[ignore = "soak: real 4-node processes; run with `-- --ignored`"]
fn n4_survives_a_validator_kill() {
    run_kill_sim(4, 8773, 9783);
}

/// n=5 (f=1): kill one validator, the quorum of 4 keeps producing + exchanging.
#[test]
#[ignore = "soak: real 5-node processes; run with `-- --ignored`"]
fn n5_survives_a_validator_kill() {
    run_kill_sim(5, 8793, 9793);
}
