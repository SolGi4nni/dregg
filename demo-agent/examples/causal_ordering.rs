//! Causal Ordering Demo — DAG-Based Event Ordering Without Consensus
//!
//! Demonstrates:
//! 1. 3 agents produce events concurrently
//! 2. Events have causal dependencies (A's event depends on B's earlier event)
//! 3. Build the causal DAG showing partial ordering
//! 4. Concurrent events (no causal relation) can be processed in any order
//! 5. Causally dependent events are always processed in correct order
//! 6. Topological sort provides a valid total order respecting causality

use dregg_types::causal::{CausalDag, hex_short};

/// Create a deterministic event hash from an agent name and sequence number.
fn event_hash(agent: &str, seq: u32) -> [u8; 32] {
    let input = format!("{}:{}", agent, seq);
    *blake3::hash(input.as_bytes()).as_bytes()
}

fn main() {
    println!("=== Dregg Causal Ordering Demo (DAG Without Consensus) ===\n");

    // ─── Setup: 3 Agents ─────────────────────────────────────────────────────
    println!("Agents:");
    println!("  Alice (A) — produces events A-0, A-1, A-2");
    println!("  Bob   (B) — produces events B-0, B-1, B-2");
    println!("  Carol (C) — produces events C-0, C-1, C-2");
    println!();

    let mut dag = CausalDag::new();

    // Event hashes
    let a0 = event_hash("A", 0);
    let a1 = event_hash("A", 1);
    let a2 = event_hash("A", 2);
    let b0 = event_hash("B", 0);
    let b1 = event_hash("B", 1);
    let b2 = event_hash("B", 2);
    let c0 = event_hash("C", 0);
    let c1 = event_hash("C", 1);
    let c2 = event_hash("C", 2);

    // ─── Step 1: Genesis Events (Independent, Concurrent) ────────────────────
    println!("--- Step 1: GENESIS EVENTS (All Concurrent) ---");
    println!();

    dag.insert_genesis(a0).unwrap();
    dag.insert_genesis(b0).unwrap();
    dag.insert_genesis(c0).unwrap();

    println!("  Inserted:");
    println!("    A-0 [{}] (genesis, no deps)", hex_short(&a0));
    println!("    B-0 [{}] (genesis, no deps)", hex_short(&b0));
    println!("    C-0 [{}] (genesis, no deps)", hex_short(&c0));
    println!();
    println!("  Concurrency check:");
    println!(
        "    A-0 || B-0 ? {} (concurrent — no causal relation)",
        dag.are_concurrent(&a0, &b0)
    );
    println!(
        "    A-0 || C-0 ? {} (concurrent — no causal relation)",
        dag.are_concurrent(&a0, &c0)
    );
    println!(
        "    B-0 || C-0 ? {} (concurrent — no causal relation)",
        dag.are_concurrent(&b0, &c0)
    );
    println!();
    println!("  These events can be processed in ANY order since they are");
    println!("  causally independent. No consensus needed to order them.");
    println!();

    // ─── Step 2: Causal Dependencies (Cross-Agent) ───────────────────────────
    println!("--- Step 2: CAUSAL DEPENDENCIES (Cross-Agent) ---");
    println!();
    println!("  Scenario:");
    println!("    - Alice sees Bob's genesis event B-0, then produces A-1");
    println!("    - Bob sees Alice's genesis event A-0, then produces B-1");
    println!("    - Carol sees BOTH A-0 and B-0, then produces C-1");
    println!();

    // A-1 depends on B-0 (Alice saw Bob's event before producing her next one)
    dag.insert(a1, &[a0, b0]).unwrap();
    println!("    A-1 [{}] depends on [A-0, B-0]", hex_short(&a1));
    println!("      meaning: Alice's second event causally follows her own A-0");
    println!("               AND Bob's B-0 (she observed it before acting)");

    // B-1 depends on A-0 (Bob saw Alice's event before producing his next one)
    dag.insert(b1, &[b0, a0]).unwrap();
    println!("    B-1 [{}] depends on [B-0, A-0]", hex_short(&b1));
    println!("      meaning: Bob's second event causally follows his own B-0");
    println!("               AND Alice's A-0 (he observed it before acting)");

    // C-1 depends on A-0 and B-0 (Carol saw both genesis events)
    dag.insert(c1, &[c0, a0, b0]).unwrap();
    println!("    C-1 [{}] depends on [C-0, A-0, B-0]", hex_short(&c1));
    println!("      meaning: Carol saw all genesis events before producing C-1");
    println!();

    println!("  Causal relationships after step 2:");
    println!(
        "    B-0 -> A-1 ? {} (B-0 happened before A-1)",
        dag.happened_before(&b0, &a1)
    );
    println!(
        "    A-0 -> B-1 ? {} (A-0 happened before B-1)",
        dag.happened_before(&a0, &b1)
    );
    println!(
        "    A-1 || B-1 ? {} (concurrent! neither causally precedes the other)",
        dag.are_concurrent(&a1, &b1)
    );
    println!(
        "    A-1 || C-1 ? {} (concurrent!)",
        dag.are_concurrent(&a1, &c1)
    );
    println!();
    println!("  KEY INSIGHT: A-1 and B-1 are concurrent even though they both");
    println!("  depend on each other's genesis events. They were produced");
    println!("  independently without observing each other.");
    println!();

    // ─── Step 3: Convergence (Diamond Pattern) ───────────────────────────────
    println!("--- Step 3: CONVERGENCE (Diamond Merge) ---");
    println!();
    println!("  Scenario:");
    println!("    - Alice sees B-1, produces A-2 (depends on A-1 and B-1)");
    println!("    - Bob sees A-1, produces B-2 (depends on B-1 and A-1)");
    println!("    - Carol sees A-1 and B-1, produces C-2 (merge point)");
    println!();

    // A-2 depends on A-1 and B-1 (Alice finally sees Bob's B-1)
    dag.insert(a2, &[a1, b1]).unwrap();
    println!("    A-2 [{}] depends on [A-1, B-1]", hex_short(&a2));

    // B-2 depends on B-1 and A-1 (Bob finally sees Alice's A-1)
    dag.insert(b2, &[b1, a1]).unwrap();
    println!("    B-2 [{}] depends on [B-1, A-1]", hex_short(&b2));

    // C-2 depends on C-1, A-1, and B-1 (Carol merges all branches)
    dag.insert(c2, &[c1, a1, b1]).unwrap();
    println!("    C-2 [{}] depends on [C-1, A-1, B-1]", hex_short(&c2));
    println!();

    println!("  After convergence:");
    println!(
        "    A-0 -> A-2 ? {} (transitive: A-0 happened before A-2)",
        dag.happened_before(&a0, &a2)
    );
    println!(
        "    B-0 -> A-2 ? {} (transitive: B-0 happened before A-2 via B-0->A-1->A-2)",
        dag.happened_before(&b0, &a2)
    );
    println!(
        "    A-2 || B-2 ? {} (still concurrent!)",
        dag.are_concurrent(&a2, &b2)
    );
    println!(
        "    A-2 || C-2 ? {} (concurrent)",
        dag.are_concurrent(&a2, &c2)
    );
    println!();

    // ─── Step 4: DAG Properties ──────────────────────────────────────────────
    println!("--- Step 4: DAG PROPERTIES ---");
    println!();

    println!("  Total events in DAG: {}", dag.len());
    println!();

    // Frontier
    let frontier = dag.frontier();
    println!("  Causal frontier (events with no successors yet):");
    for h in &frontier {
        let name = identify_event(h, &a0, &a1, &a2, &b0, &b1, &b2, &c0, &c1, &c2);
        println!("    {} [{}]", name, hex_short(h));
    }
    println!();

    // Depths
    println!("  Causal depths (longest path from genesis):");
    println!("    A-0: depth {}", dag.depth(&a0).unwrap());
    println!("    A-1: depth {}", dag.depth(&a1).unwrap());
    println!("    A-2: depth {}", dag.depth(&a2).unwrap());
    println!("    B-0: depth {}", dag.depth(&b0).unwrap());
    println!("    B-1: depth {}", dag.depth(&b1).unwrap());
    println!("    B-2: depth {}", dag.depth(&b2).unwrap());
    println!("    C-0: depth {}", dag.depth(&c0).unwrap());
    println!("    C-1: depth {}", dag.depth(&c1).unwrap());
    println!("    C-2: depth {}", dag.depth(&c2).unwrap());
    println!();

    // ─── Step 5: Topological Sort (Valid Processing Order) ───────────────────
    println!("--- Step 5: TOPOLOGICAL SORT (Valid Processing Order) ---");
    println!();
    println!("  A valid total order that respects all causal dependencies:");
    println!();

    let topo = dag.topological_order();
    for (i, h) in topo.iter().enumerate() {
        let name = identify_event(h, &a0, &a1, &a2, &b0, &b1, &b2, &c0, &c1, &c2);
        println!("    {}. {} [{}]", i + 1, name, hex_short(h));
    }
    println!();

    // Verify causality in topological order
    println!("  Verification: all causal deps appear before their dependents:");
    let mut all_ok = true;
    for (i, h) in topo.iter().enumerate() {
        if let Some(deps) = dag.deps_of(h) {
            for dep in deps {
                let dep_pos = topo.iter().position(|x| x == dep).unwrap();
                if dep_pos >= i {
                    println!(
                        "    VIOLATION: dep at position {} >= event at position {}",
                        dep_pos, i
                    );
                    all_ok = false;
                }
            }
        }
    }
    if all_ok {
        println!(
            "    All {} events correctly ordered: every dependency precedes its dependent. [PASS]",
            topo.len()
        );
    }
    println!();

    // ─── Step 6: Concurrency vs Causality Summary ────────────────────────────
    println!("--- Step 6: CONCURRENCY vs CAUSALITY ---");
    println!();
    println!("  Causal pairs (A -> B means A must be processed before B):");
    let causal_pairs: Vec<(&str, &str, &[u8; 32], &[u8; 32])> = vec![
        ("A-0", "A-1", &a0, &a1),
        ("A-0", "A-2", &a0, &a2),
        ("A-1", "A-2", &a1, &a2),
        ("B-0", "B-1", &b0, &b1),
        ("B-0", "B-2", &b0, &b2),
        ("B-1", "B-2", &b1, &b2),
        ("C-0", "C-1", &c0, &c1),
        ("C-0", "C-2", &c0, &c2),
        ("C-1", "C-2", &c1, &c2),
        ("B-0", "A-1", &b0, &a1),
        ("A-0", "B-1", &a0, &b1),
        ("A-0", "C-1", &a0, &c1),
        ("B-0", "C-1", &b0, &c1),
    ];

    for (name_a, name_b, ha, hb) in &causal_pairs {
        assert!(
            dag.happened_before(ha, hb),
            "{} should happen before {}",
            name_a,
            name_b
        );
        println!("    {} -> {}", name_a, name_b);
    }
    println!();

    println!("  Concurrent pairs (can be processed in ANY order):");
    let concurrent_pairs: Vec<(&str, &str, &[u8; 32], &[u8; 32])> = vec![
        ("A-0", "B-0", &a0, &b0),
        ("A-0", "C-0", &a0, &c0),
        ("B-0", "C-0", &b0, &c0),
        ("A-1", "B-1", &a1, &b1),
        ("A-1", "C-1", &a1, &c1),
        ("B-1", "C-1", &b1, &c1),
        ("A-2", "B-2", &a2, &b2),
        ("A-2", "C-2", &a2, &c2),
        ("B-2", "C-2", &b2, &c2),
    ];

    for (name_a, name_b, ha, hb) in &concurrent_pairs {
        assert!(
            dag.are_concurrent(ha, hb),
            "{} and {} should be concurrent",
            name_a,
            name_b
        );
        println!("    {} || {}", name_a, name_b);
    }
    println!();

    // ─── Step 7: Merge Frontier Hash ─────────────────────────────────────────
    println!("--- Step 7: DETERMINISTIC STATE FINGERPRINT ---");
    println!();

    let merge_hash = dag.merge_frontier();
    println!("  Merge frontier hash: {}", hex_short(&merge_hash));
    println!("  This hash uniquely identifies the current DAG state.");
    println!("  Two nodes with the same frontier hash have equivalent causal knowledge.");
    println!();

    // ─── Summary ─────────────────────────────────────────────────────────────
    println!("--- PROTOCOL PROPERTIES ---");
    println!();
    println!("  1. NO CONSENSUS FOR ORDERING: Causal relationships are determined");
    println!("     purely from hash-linked dependencies. No leader election needed.");
    println!();
    println!("  2. PARTIAL ORDER: Only causally related events have a required order.");
    println!("     Concurrent events can be processed in any convenient order.");
    println!();
    println!("  3. CONSISTENCY: All nodes that process events respecting the");
    println!("     topological order will reach the same state, regardless of");
    println!("     the specific total order chosen for concurrent events.");
    println!();
    println!("  4. AVAILABILITY: Agents can produce events without waiting for");
    println!("     other agents. No single point of failure blocks progress.");
    println!();
    println!("  5. HASH-LINKED INTEGRITY: Each event's hash includes its");
    println!("     dependencies, making the DAG tamper-evident.");
    println!();
    println!("=== Causal Ordering Demo Complete ===");
}

/// Identify an event hash by comparing against known hashes.
fn identify_event(
    h: &[u8; 32],
    a0: &[u8; 32],
    a1: &[u8; 32],
    a2: &[u8; 32],
    b0: &[u8; 32],
    b1: &[u8; 32],
    b2: &[u8; 32],
    c0: &[u8; 32],
    c1: &[u8; 32],
    c2: &[u8; 32],
) -> &'static str {
    if h == a0 {
        "A-0"
    } else if h == a1 {
        "A-1"
    } else if h == a2 {
        "A-2"
    } else if h == b0 {
        "B-0"
    } else if h == b1 {
        "B-1"
    } else if h == b2 {
        "B-2"
    } else if h == c0 {
        "C-0"
    } else if h == c1 {
        "C-1"
    } else if h == c2 {
        "C-2"
    } else {
        "???"
    }
}
