//! The reactive agent — Decision 3's triad in one binary.
//!
//!   cells are LAW       a worker-mandate cell: budget slice, pinned tool
//!                        scope, one-way revocation — every bound enforced by
//!                        the cell program in the EXECUTOR, not by this code;
//!   agents are WILL     this process: subscribe → decide → turn;
//!   receipts are the    the node's committed-receipt stream in
//!   NERVOUS SYSTEM      (`/api/events/stream`), the reaction's own receipt
//!                        out — both the public `Receipt` noun.
//!
//! Run a node (see QUICKSTART), then:
//!
//!   DREGG_NODE_URL=http://localhost:8421 \
//!     cargo run -p dregg-sdk --example reactive_agent
//!
//!   DREGG_WATCH_CELL=<hex cell id>   react only to that cell's receipts
//!                                    (default: every committed receipt)
//!
//! The same stream is curl-able: `curl -N $DREGG_NODE_URL/api/events/stream`.

#[cfg(all(feature = "federation-client", feature = "network"))]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    use dregg_cell::Cell;
    use dregg_sdk::events::{NodeEvents, ReceiptFilter};
    use dregg_sdk::factories::ADOPT_TURN_FEE;
    use dregg_sdk::polis::{
        WorkerMandate, activate_worker, spawn_worker_mandate, tool_scope_commitment, worker_spend,
    };
    use dregg_sdk::{AgentCipherclerk, AgentRuntime};
    use dregg_types::hex_encode;

    let node_url =
        std::env::var("DREGG_NODE_URL").unwrap_or_else(|_| "http://localhost:8421".into());

    // ── law: birth the worker-mandate cell ─────────────────────────────────
    // The orchestrator delegates a 50-computron slice under a pinned tool
    // scope. The slice IS the cell's balance: overspend cannot commit
    // (conservation), revocation is terminal (the program), and every
    // reaction receipt resolves to these content-addressed terms.
    let mut runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), "reactive-agent");
    let orchestrator = runtime.cell_id();
    let owner_pubkey = runtime
        .cipherclerk()
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .public_key()
        .0;
    let mandate = WorkerMandate {
        orchestrator,
        slice: 50,
        tool_scope: tool_scope_commitment(&["transfer"]),
        worker_tag: *blake3::hash(b"reactive-agent example worker").as_bytes(),
    };
    let plan = spawn_worker_mandate(&mandate, owner_pubkey, [0x07; 32], orchestrator)?;
    let worker = plan.cell_id;
    runtime.deploy_factory(plan.descriptor.clone());
    runtime
        .turn()
        .effects(plan.create_effects.clone())
        .sign()?
        .submit()?;
    runtime
        .turn()
        .effects(plan.fund_effects.clone())
        .sign()?
        .submit()?;
    runtime
        .turn()
        .as_cell(worker, ADOPT_TURN_FEE)
        .effects(plan.adopt_effects.clone())
        .sign()?
        .submit()?;
    runtime
        .turn()
        .on(worker)
        .effects(activate_worker(worker, &mandate))
        .sign()?
        .submit()?;

    // The cell the worker pays on each observation.
    let beneficiary = {
        let cell = Cell::with_balance([0xBE; 32], [0u8; 32], 0);
        let id = cell.id();
        runtime.ledger().lock().unwrap().insert_cell(cell)?;
        id
    };
    println!("worker mandate cell : {worker} (slice 50, ACTIVE)");
    println!("beneficiary cell    : {beneficiary}\n");

    // ── nervous system: subscribe to the node's committed receipts ─────────
    let node = NodeEvents::new(&node_url);
    let filter = match std::env::var("DREGG_WATCH_CELL") {
        Ok(cell) => ReceiptFilter::default().cell_hex(cell),
        Err(_) => ReceiptFilter::default(),
    };
    let mut receipts = node.subscribe(filter);
    println!("watching {node_url}/api/events/stream …\n");

    // ── will: react to each observation with a mandate-bounded spend ───────
    while let Some(observed) = receipts.next().await {
        println!(
            "observed  turn {} (agent {}, finality {})",
            hex_encode(&observed.turn_hash),
            hex_encode(&observed.agent.0),
            format!("{:?}", observed.finality).to_lowercase(),
        );
        // The reaction is an ordinary authorized turn; whether it COMMITS is
        // the mandate cell's law. After five reactions the slice is spent and
        // the executor refuses the sixth — will, bounded.
        match runtime
            .turn()
            .on(worker)
            .effects(worker_spend(worker, beneficiary, 10))
            .sign()?
            .submit()
        {
            Ok(reaction) => println!(
                "reacted   spend 10 from the slice — receipt {}\n",
                hex_encode(&reaction.receipt_hash()),
            ),
            Err(refused) => println!("refused   by the mandate's law: {refused}\n"),
        }
    }
    Ok(())
}

#[cfg(not(all(feature = "federation-client", feature = "network")))]
fn main() {
    eprintln!("reactive_agent needs the default `federation-client` + `network` features");
}
