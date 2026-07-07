//! n3_plateau_probe.rs — THROWAWAY diagnostic (root-cause of the n=3 sustained-finality plateau).
//!
//! NOT a product test. Clones the `sustained_finality.rs` launch scaffolding but,
//! instead of only watching `latest_height` (attested-root / turn height), it polls
//! the FULL structural triple on every node while turn 3 is outstanding:
//!   * `dag_height`   — max block seq in the local lace (advances on EVERY block).
//!   * `block_count`  — number of blocks in the local lace.
//!   * `latest_height`— attested-root / turn height (turn-bearing finality only).
//!
//! The discriminator: at the turn-3 plateau, if `dag_height`/`block_count` KEEP
//! GROWING while `latest_height` is stuck, blocks are being produced+disseminated
//! but the turn is not finalizing/executing (an ordering/execute gap). If
//! `dag_height`/`block_count` are ALSO FROZEN, the DAG stopped advancing entirely —
//! a PRODUCE-Wait wedge (no round cohort advances) or a faucet-drop (the turn never
//! entered consensus, so quiescence is correct).

#![allow(dead_code)]
use std::io::Read;
use std::net::TcpStream;
use std::process::{Child, Command};
use std::time::{Duration, Instant};

const NODE_BIN: &str = env!("CARGO_BIN_EXE_dregg-node");

struct NodeProc {
    child: Child,
    http: u16,
    name: &'static str,
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
fn u64f(port: u16, field: &str) -> u64 {
    http_get(port, "/status")
        .and_then(|b| json_field(&b, field).map(|s| s.to_string()))
        .and_then(|s| s.parse().ok())
        .unwrap_or(0)
}
/// (dag_height, block_count, latest_height)
fn triple(port: u16) -> (u64, u64, u64) {
    (
        u64f(port, "dag_height"),
        u64f(port, "block_count"),
        u64f(port, "latest_height"),
    )
}
fn cell_found(port: u16, cell_hex: &str) -> bool {
    http_get(port, &format!("/api/cell/{cell_hex}"))
        .map(|b| json_field(&b, "found") == Some("true"))
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
fn run_genesis(tmp: &std::path::Path) {
    let status = Command::new(NODE_BIN)
        .args(["genesis", "--validators", "3", "--output"])
        .arg(tmp)
        .status()
        .expect("spawn genesis");
    assert!(status.success());
}
fn launch(
    name: &'static str,
    data_dir: &std::path::Path,
    idx: usize,
    http: u16,
    gossip: u16,
    peers: &str,
    faucet: bool,
) -> NodeProc {
    let log = data_dir.join("stderr.log");
    let log_file = std::fs::File::create(&log).unwrap();
    let mut cmd = Command::new(NODE_BIN);
    cmd.arg("run")
        .arg("--data-dir")
        .arg(data_dir)
        .args(["--key-file", "node.key"])
        .args(["--node-index", &idx.to_string()])
        .args(["--federation-size", "3"])
        .args(["--port", &http.to_string()])
        .args(["--gossip-port", &gossip.to_string()])
        .args(["--bind", "127.0.0.1"])
        .args(["--federation-peers", peers])
        .args(["--federation-mode", "full"])
        .args(["--consensus", "blocklace"])
        .args(["--idle-heartbeat-ms", "2000"])
        .args(["--block-cadence-ms", "1000"])
        .env("DREGG_LEAN_PRODUCER", "0")
        .env(
            "RUST_LOG",
            "warn,dregg_node::blocklace_sync=debug,dregg_blocklace=debug",
        )
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::from(log_file));
    if faucet {
        cmd.arg("--enable-faucet");
    }
    NodeProc {
        child: cmd.spawn().unwrap(),
        http,
        name,
        log,
    }
}
fn post_faucet(port: u16, recipient: &str, amount: u64) -> bool {
    let body = format!("{{\"recipient\":\"{recipient}\",\"amount\":{amount}}}");
    let Ok(mut stream) = TcpStream::connect(("127.0.0.1", port)) else {
        return false;
    };
    let _ = stream.set_read_timeout(Some(Duration::from_secs(5)));
    let _ = stream.set_write_timeout(Some(Duration::from_secs(5)));
    let req = format!(
        "POST /api/faucet HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
        body.len(),
        body
    );
    use std::io::Write;
    if stream.write_all(req.as_bytes()).is_err() {
        return false;
    }
    let mut resp = String::new();
    let _ = stream.read_to_string(&mut resp);
    resp.contains("\"success\":true")
}
fn recipient_for(turn: usize) -> String {
    let mut b = [0u8; 32];
    b[0] = 0xC0;
    b[31] = turn as u8;
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// Load node-0's persisted DAG, reconstruct DAG-depth rounds (1 + max pred round),
/// and report: per-creator counts, per-round cohort sizes, any creator with a
/// DUPLICATE block at the same round (the leader-skip / equivocation hazard), and
/// where each TURN block sits vs. which waves the finalized order covers.
fn analyze_dag(data_dir: &std::path::Path) {
    use dregg_blocklace::finality::{Block, BlockId, Payload};
    use std::collections::HashMap;

    let db = data_dir.join("dregg.redb");
    let store = match dregg_persist::PersistentStore::open(&db) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[dag] could not open store {db:?}: {e}");
            return;
        }
    };
    let blocks: Vec<Block> = match store.load_all_blocks() {
        Ok(b) => b,
        Err(e) => {
            eprintln!("[dag] load_all_blocks failed: {e}");
            return;
        }
    };
    let by_id: HashMap<BlockId, &Block> = blocks.iter().map(|b| (b.id(), b)).collect();

    // Reconstruct DAG-depth rounds by repeated relaxation (small DAG).
    let mut round: HashMap<BlockId, u64> = HashMap::new();
    for _ in 0..(blocks.len() + 2) {
        let mut changed = false;
        for b in &blocks {
            let r = if b.predecessors.iter().all(|p| !by_id.contains_key(p)) {
                1
            } else {
                1 + b
                    .predecessors
                    .iter()
                    .filter_map(|p| round.get(p).copied())
                    .max()
                    .unwrap_or(0)
            };
            if round.get(&b.id()) != Some(&r) {
                round.insert(b.id(), r);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let creators: std::collections::BTreeSet<[u8; 32]> = blocks.iter().map(|b| b.creator).collect();
    eprintln!("[dag] {} blocks, {} creators", blocks.len(), creators.len());
    for (ci, c) in creators.iter().enumerate() {
        let n = blocks.iter().filter(|b| &b.creator == c).count();
        let turns = blocks
            .iter()
            .filter(|b| {
                &b.creator == c && matches!(b.payload, Payload::Turn(_) | Payload::TurnBundle(_))
            })
            .count();
        eprintln!(
            "  creator[{ci}] {}… authored {n} blocks ({turns} turn-bearing)",
            hex8(c)
        );
    }

    // Per-round cohort + duplicate detection.
    let max_r = round.values().copied().max().unwrap_or(0);
    let mut dup_found = false;
    for r in 1..=max_r {
        let here: Vec<&Block> = blocks
            .iter()
            .filter(|b| round.get(&b.id()) == Some(&r))
            .collect();
        let mut per_creator: HashMap<[u8; 32], usize> = HashMap::new();
        for b in &here {
            *per_creator.entry(b.creator).or_default() += 1;
        }
        let dups: Vec<String> = per_creator
            .iter()
            .filter(|(_, n)| **n > 1)
            .map(|(c, n)| format!("{}…×{n}", hex8(c)))
            .collect();
        let turns_here: Vec<String> = here
            .iter()
            .filter(|b| matches!(b.payload, Payload::Turn(_) | Payload::TurnBundle(_)))
            .map(|b| format!("{}…", hex8(&b.creator)))
            .collect();
        let wave = (r - 1) / 3;
        let is_leader_round = (r - 1) % 3 == 0;
        let marker = if is_leader_round {
            format!(" [wave {wave} START/leader round]")
        } else {
            String::new()
        };
        if !dups.is_empty() || !turns_here.is_empty() || is_leader_round {
            eprintln!(
                "  round {r:<2} cohort={} distinct_creators={}{} turns={turns_here:?}{}",
                here.len(),
                per_creator.len(),
                if dups.is_empty() {
                    String::new()
                } else {
                    format!(" DUPLICATES={dups:?}")
                },
                marker
            );
        }
        if !dups.is_empty() {
            dup_found = true;
        }
    }
    eprintln!(
        "[dag] duplicate-same-round-block (leader-skip / equivocation) present = {dup_found}"
    );

    // Predecessor-count per round: full-cohort citation (zero-slack) means every
    // non-genesis block cites all 3 of the previous round's blocks.
    for r in 1..=max_r.min(16) {
        let here: Vec<&Block> = blocks
            .iter()
            .filter(|b| round.get(&b.id()) == Some(&r))
            .collect();
        let npreds: Vec<usize> = here
            .iter()
            .map(|b| {
                b.predecessors
                    .iter()
                    .filter(|p| by_id.contains_key(p))
                    .count()
            })
            .collect();
        if r <= 2 || (10..=13).contains(&r) {
            eprintln!("  round {r:<2} in-lace pred counts = {npreds:?}");
        }
    }

    // Run tau ON THIS EXACT LIVE DAG (the ordering projection the node uses).
    let participants: Vec<[u8; 32]> = creators.iter().copied().collect();
    let mut ordering_lace = dregg_blocklace::Blocklace::new();
    let mut to_ord: HashMap<BlockId, dregg_blocklace::BlockId> = HashMap::new();
    let mut to_cs: HashMap<dregg_blocklace::BlockId, ([u8; 32], u64, bool)> = HashMap::new();
    let mut sorted: Vec<&Block> = blocks.iter().collect();
    sorted.sort_by(|a, b| a.seq.cmp(&b.seq).then(a.creator.cmp(&b.creator)));
    for b in sorted {
        let preds: Vec<dregg_blocklace::BlockId> = b
            .predecessors
            .iter()
            .filter_map(|p| to_ord.get(p).copied())
            .collect();
        let is_turn = matches!(b.payload, Payload::Turn(_) | Payload::TurnBundle(_));
        let payload = match &b.payload {
            Payload::Turn(d) => d.clone(),
            Payload::TurnBundle(t) => t.signed_turn.clone(),
            _ => vec![],
        };
        let ob = dregg_blocklace::Block::new(b.creator, b.seq, preds, payload);
        let oid = ob.id();
        let _ = ordering_lace.insert_unverified(ob);
        to_ord.insert(b.id(), oid);
        to_cs.insert(oid, (b.creator, b.seq, is_turn));
    }
    let order = dregg_blocklace::ordering::tau(&ordering_lace, &participants);
    let turns_finalized: Vec<(String, u64)> = order
        .iter()
        .filter_map(|oid| to_cs.get(oid))
        .filter(|(_, _, t)| *t)
        .map(|(c, s, _)| (hex8(c), *s))
        .collect();
    eprintln!(
        "[dag] tau on the LIVE DAG finalizes {} of {} blocks; turn blocks finalized = {:?}",
        order.len(),
        blocks.len(),
        turns_finalized
    );

    // ORDER SENSITIVITY: the wave-leader round-robin is `participants[wave % n]`, so
    // the participant ORDER decides which creator leads each wave. Try every
    // permutation of the 3 creators and report how many turns each order finalizes.
    let cs: Vec<[u8; 32]> = creators.iter().copied().collect();
    let perms = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    for p in perms {
        let parts: Vec<[u8; 32]> = p.iter().map(|&i| cs[i]).collect();
        let ord = dregg_blocklace::ordering::tau(&ordering_lace, &parts);
        let nturns = ord
            .iter()
            .filter_map(|oid| to_cs.get(oid))
            .filter(|(_, _, t)| *t)
            .count();
        eprintln!(
            "  perm {:?} (leaders w0={} w1={} w2={} w3={}): finalizes {} blocks, {} turns",
            p,
            hex8(&parts[0]),
            hex8(&parts[1]),
            hex8(&parts[2]),
            hex8(&parts[0]),
            ord.len(),
            nturns
        );
    }
}

fn hex8(b: &[u8; 32]) -> String {
    b[..4].iter().map(|x| format!("{x:02x}")).collect()
}

#[test]
fn probe_n3_turn3_plateau_structure() {
    let tmp = tempfile::tempdir().unwrap();
    let gen_dir = tmp.path().join("genesis");
    std::fs::create_dir_all(&gen_dir).unwrap();
    run_genesis(&gen_dir);
    for i in 0..3usize {
        let d = tmp.path().join(format!("node-{i}"));
        std::fs::create_dir_all(&d).unwrap();
        std::fs::copy(gen_dir.join("genesis.json"), d.join("genesis.json")).unwrap();
        let _ = std::fs::copy(gen_dir.join(".devnet"), d.join(".devnet"));
        std::fs::copy(gen_dir.join(format!("node-{i}.key")), d.join("node.key")).unwrap();
    }
    let (h0, h1, h2) = (8683u16, 8684u16, 8685u16);
    let (g0, g1, g2) = (9783u16, 9784u16, 9785u16);
    let mut n0 = launch(
        "node-0",
        &tmp.path().join("node-0"),
        0,
        h0,
        g0,
        &format!("127.0.0.1:{g1},127.0.0.1:{g2}"),
        true,
    );
    std::thread::sleep(Duration::from_secs(1));
    let n1 = launch(
        "node-1",
        &tmp.path().join("node-1"),
        1,
        h1,
        g1,
        &format!("127.0.0.1:{g0},127.0.0.1:{g2}"),
        false,
    );
    let n2 = launch(
        "node-2",
        &tmp.path().join("node-2"),
        2,
        h2,
        g2,
        &format!("127.0.0.1:{g0},127.0.0.1:{g1}"),
        false,
    );
    let ports = [h0, h1, h2];
    for (nm, p) in [("node-0", h0), ("node-1", h1), ("node-2", h2)] {
        assert!(wait_for_port(p, 40), "{nm} never came up");
    }
    std::thread::sleep(Duration::from_secs(8));

    // Turns 1 and 2: drive them to commit (short bounded wait).
    for turn in 1..=2usize {
        let r = recipient_for(turn);
        assert!(post_faucet(h0, &r, 100), "turn {turn} faucet submit");
        let deadline = Instant::now() + Duration::from_secs(30);
        let mut ok = false;
        while Instant::now() < deadline {
            std::thread::sleep(Duration::from_secs(1));
            if ports.iter().all(|&p| cell_found(p, &r)) {
                ok = true;
                break;
            }
        }
        eprintln!(
            "[turn {turn}] committed={ok} triples(dag,blk,latest)={:?}",
            ports.map(triple)
        );
    }

    // Turn 3: submit, then WATCH the structural triple every second for 25s.
    let r3 = recipient_for(3);
    let submitted = post_faucet(h0, &r3, 100);
    eprintln!("[turn 3] faucet POST success={submitted}");
    let before = ports.map(triple);
    eprintln!(
        "[turn 3] t=0  triples(dag,blk,latest)={before:?}  cell_found={:?}",
        ports.map(|p| cell_found(p, &r3))
    );
    for t in 1..=25 {
        std::thread::sleep(Duration::from_secs(1));
        if t % 3 == 0 || t == 25 {
            eprintln!(
                "[turn 3] t={t:<2} triples(dag,blk,latest)={:?}  cell_found={:?}",
                ports.map(triple),
                ports.map(|p| cell_found(p, &r3))
            );
        }
    }
    // ── POST-PLATEAU DAG DUMP: stop node-0 to release the redb single-writer
    //    lock, open its store, reconstruct the DAG. (Kill the child directly so the
    //    `NodeProc` value stays alive for the log scan below.)
    let node0_dir = tmp.path().join("node-0");
    let _ = n0.child.kill();
    let _ = n0.child.wait();
    std::thread::sleep(Duration::from_secs(2));
    analyze_dag(&node0_dir);

    let after = ports.map(triple);
    let dag_grew = before.iter().zip(after.iter()).any(|(b, a)| a.0 > b.0);
    let blk_grew = before.iter().zip(after.iter()).any(|(b, a)| a.1 > b.1);
    eprintln!(
        "[turn 3] VERDICT: dag_height grew during plateau = {dag_grew}; block_count grew = {blk_grew}"
    );
    eprintln!("  before={before:?}\n  after ={after:?}");
    // Scan each node's log for finalization/divergence/equivocation diagnostics.
    for np in [&n0, &n1, &n2] {
        let log = std::fs::read_to_string(&np.log).unwrap_or_default();
        let produced = log.matches("produced round-disciplined block").count();
        let seqs: Vec<&str> = log
            .lines()
            .filter(|l| l.contains("produced round-disciplined block"))
            .collect();
        let last_seqs: Vec<String> = seqs
            .iter()
            .rev()
            .take(6)
            .rev()
            .map(|l| {
                l.split("seq=")
                    .nth(1)
                    .map(|s| s.split_whitespace().next().unwrap_or("?").to_string())
                    .unwrap_or_default()
            })
            .collect();
        let signals: Vec<&str> = log
            .lines()
            .filter(|l| {
                l.contains("finalized turn executed")
                    || l.contains("finalized turn rejected")
                    || l.contains("DIVERGENCE")
                    || l.contains("FALLING BACK")
                    || l.contains("UNAVAILABLE")
                    || l.contains("finality gate REFUSED")
                    || l.contains("PREFIX SHIFTED")
                    || l.contains("strand-admission")
                    || l.contains("differential")
            })
            .collect();
        eprintln!(
            "[{}] produced {produced} round blocks (last seqs: {last_seqs:?}); {} signal lines:",
            np.name,
            signals.len()
        );
        for l in signals.iter().rev().take(12).rev() {
            eprintln!("    {l}");
        }
    }
}
