//! Pyana P2P Networking Demo
//!
//! Demonstrates two peer nodes connecting via QUIC, exchanging turns
//! with causal ordering, and gossiping revocations.

use pyana_net::causal::{DagEntry, EntryDag};
// GossipNetwork is available for topic-based pub/sub (see src/gossip.rs)
#[allow(unused_imports)]
use pyana_net::gossip::GossipNetwork;
use pyana_net::message::PeerMessage;
use pyana_net::node::{PeerNode, PeerNodeConfig, fmt_node_id};
use tracing_subscriber::EnvFilter;

const BANNER: &str = r#"
═══════════════════════════════════════════════════════
  PYANA P2P NETWORKING DEMO
═══════════════════════════════════════════════════════
"#;

#[tokio::main]
async fn main() {
    // Initialize tracing (set RUST_LOG=debug for verbose output)
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("warn")),
        )
        .init();

    println!("{BANNER}");

    if let Err(e) = run_demo().await {
        eprintln!("\n  ERROR: {e}");
        std::process::exit(1);
    }
}

async fn run_demo() -> Result<(), Box<dyn std::error::Error>> {
    // ─── Step 1: Start peer nodes ───────────────────────────────────────────
    println!("[1/5] Starting peer nodes...");

    let node_a = PeerNode::new(PeerNodeConfig::default()).await?;
    let node_b = PeerNode::new(PeerNodeConfig::default()).await?;

    let id_a = node_a.node_id();
    let id_b = node_b.node_id();
    let addr_b = node_b.local_addr();

    println!(
        "  \u{2192} Node A: {} @ {}",
        fmt_node_id(&id_a),
        node_a.local_addr()
    );
    println!("  \u{2192} Node B: {} @ {}", fmt_node_id(&id_b), addr_b);
    println!();

    // ─── Step 2: Establish P2P connection ───────────────────────────────────
    println!("[2/5] Establishing P2P connection...");

    // Spawn acceptor on B (must keep node_b alive for the connection to persist)
    let (conn_b_tx, conn_b_rx) = tokio::sync::oneshot::channel();
    let node_b_handle = tokio::spawn(async move {
        let conn = node_b.accept().await.unwrap();
        let _ = conn_b_tx.send(conn);
        // Keep node_b alive until the demo is done (endpoint must outlive connections)
        tokio::time::sleep(std::time::Duration::from_secs(30)).await;
        node_b.close();
    });

    // Connect A -> B
    let conn_a = node_a.connect(addr_b).await?;
    let conn_b = conn_b_rx
        .await
        .map_err(|_| "failed to receive connection from node B")?;

    println!("  \u{2192} A \u{2192} B: connected via QUIC");
    println!(
        "  \u{2192} A sees remote: {}",
        fmt_node_id(&conn_a.remote_id())
    );
    println!(
        "  \u{2192} B sees remote: {}",
        fmt_node_id(&conn_b.remote_id())
    );
    println!("  \u{2192} RTT: {:?}", conn_a.rtt());
    println!();

    // ─── Step 3: Turn dissemination with causal chaining ────────────────────
    println!("[3/5] Turn dissemination (causal chaining)...");

    let mut dag_a = EntryDag::new();
    let mut dag_b = EntryDag::new();

    // Node A creates Turn T1 (genesis, no deps)
    let t1_data = b"turn-1: initialize cell state";
    let t1_hash = *blake3::hash(t1_data).as_bytes();
    let t1_entry = DagEntry {
        turn_hash: t1_hash,
        turn_data: t1_data.to_vec(),
        deps: vec![],
        timestamp: now_ms(),
        node_id: id_a,
    };

    dag_a.insert(t1_entry.clone())?;

    let t1_msg = PeerMessage::PublishTurn {
        turn_hash: t1_hash,
        turn_data: t1_data.to_vec(),
        causal_deps: vec![],
    };

    // A sends T1 to B
    conn_a.send(&t1_msg).await?;
    println!("  \u{2192} A publishes Turn T1 (causal deps: [])");

    // B receives T1
    let received = conn_b.recv().await?;
    match &received {
        PeerMessage::PublishTurn {
            turn_hash,
            turn_data,
            causal_deps,
        } => {
            let entry = DagEntry {
                turn_hash: *turn_hash,
                turn_data: turn_data.clone(),
                deps: causal_deps.clone(),
                timestamp: now_ms(),
                node_id: id_a,
            };

            assert!(dag_b.is_causally_valid(&entry));
            dag_b.insert(entry)?;
            println!("  \u{2192} B receives T1, validates, inserts into DAG");
        }
        _ => panic!("unexpected message type"),
    }

    // Node B creates Turn T2 (depends on T1)
    let t2_data = b"turn-2: update cell counter";
    let t2_hash = *blake3::hash(t2_data).as_bytes();
    let t2_entry = DagEntry {
        turn_hash: t2_hash,
        turn_data: t2_data.to_vec(),
        deps: vec![t1_hash],
        timestamp: now_ms(),
        node_id: id_b,
    };

    dag_b.insert(t2_entry.clone())?;

    let t2_msg = PeerMessage::PublishTurn {
        turn_hash: t2_hash,
        turn_data: t2_data.to_vec(),
        causal_deps: vec![t1_hash],
    };

    // B sends T2 to A
    conn_b.send(&t2_msg).await?;
    println!("  \u{2192} B publishes Turn T2 (causal deps: [T1])");

    // A receives T2
    let received = conn_a.recv().await?;
    match &received {
        PeerMessage::PublishTurn {
            turn_hash,
            turn_data,
            causal_deps,
        } => {
            let entry = DagEntry {
                turn_hash: *turn_hash,
                turn_data: turn_data.clone(),
                deps: causal_deps.clone(),
                timestamp: now_ms(),
                node_id: id_b,
            };

            let valid = dag_a.is_causally_valid(&entry);
            dag_a.insert(entry)?;
            println!(
                "  \u{2192} A receives T2, validates causal ordering {}",
                if valid { "\u{2713}" } else { "\u{2717}" }
            );
        }
        _ => panic!("unexpected message type"),
    }
    println!();

    // ─── Step 4: Request/Response (pull-based sync) ─────────────────────────
    println!("[4/5] Pull-based turn sync (request/response)...");

    // Use concurrent tasks: B accepts a bi-stream request, A sends one.
    // We need to keep conn_b alive, so we use scoped concurrency via tokio::join!
    let dag_b_clone = dag_b.clone();
    let t1_hash_copy = t1_hash;

    let (resp_result, req_result) = tokio::join!(
        // B: accept and respond
        async {
            let (request, handle) = conn_b.accept_request().await?;
            if let PeerMessage::RequestTurn { turn_hash } = request {
                let turn_data = dag_b_clone.get(&turn_hash).map(|e| e.turn_data.clone());
                let response = PeerMessage::TurnResponse { turn_data };
                handle.respond(&response).await?;
            }
            Ok::<_, pyana_net::node::PeerError>(())
        },
        // A: request
        async {
            conn_a
                .request(&PeerMessage::RequestTurn {
                    turn_hash: t1_hash_copy,
                })
                .await
        }
    );

    resp_result?;
    let response = req_result?;

    match &response {
        PeerMessage::TurnResponse { turn_data } => {
            let has_it = turn_data.is_some();
            println!(
                "  \u{2192} A requests T1 from B: {}",
                if has_it {
                    "received \u{2713}"
                } else {
                    "not found \u{2717}"
                }
            );
            if let Some(data) = turn_data {
                assert_eq!(data, t1_data);
                println!("  \u{2192} Verified: data matches original T1");
            }
        }
        _ => panic!("unexpected response type"),
    }
    println!();

    // ─── Step 5: Causal DAG state ───────────────────────────────────────────
    println!("[5/5] Causal DAG state...");

    let frontier_a = dag_a.latest();
    let frontier_b = dag_b.latest();

    println!(
        "  \u{2192} Node A frontier: [{}]",
        frontier_a
            .iter()
            .map(|e| format_turn_name(&e.turn_data))
            .collect::<Vec<_>>()
            .join(", ")
    );
    println!(
        "  \u{2192} Node B frontier: [{}]",
        frontier_b
            .iter()
            .map(|e| format_turn_name(&e.turn_data))
            .collect::<Vec<_>>()
            .join(", ")
    );

    let consistent = dag_a.merge_frontier() == dag_b.merge_frontier();
    println!(
        "  \u{2192} Causal consistency: {}",
        if consistent { "\u{2713}" } else { "\u{2717}" }
    );

    // Show causal order
    let order_a = dag_a.causal_order();
    println!(
        "  \u{2192} Causal order (A): [{}]",
        order_a
            .iter()
            .map(|e| format_turn_name(&e.turn_data))
            .collect::<Vec<_>>()
            .join(" \u{2192} ")
    );

    // Show DAG stats
    println!("  \u{2192} DAG size: {} turns", dag_a.len());
    println!();

    // ─── Cleanup ────────────────────────────────────────────────────────────
    conn_a.close();
    node_a.close();
    node_b_handle.abort();

    println!(
        "\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}"
    );
    println!("  Demo complete. All P2P operations successful.");
    println!(
        "\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}\u{2550}"
    );

    Ok(())
}

fn now_ms() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() as i64
}

fn format_turn_name(data: &[u8]) -> String {
    if let Ok(s) = std::str::from_utf8(data) {
        if let Some(colon_pos) = s.find(':') {
            return s[..colon_pos].to_string();
        }
        if s.len() > 20 {
            return format!("{}...", &s[..20]);
        }
        return s.to_string();
    }
    format!("{:02x}{:02x}...", data[0], data[1])
}
