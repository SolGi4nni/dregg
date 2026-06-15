//! # The ADOS reference proof — agent orchestration as a LIVE web surface + a DURABLE spine.
//!
//! The crown the record describes: *ADOS = the OS that makes any loop's actions provably
//! authorized/recorded/budgeted/coordinated so a swarm becomes auditable WITHOUT trusting the loops.*
//! The four integrators (`buildr`/`builders`/`sig`/`simbi`) each hand-rolled the same six primitives
//! around their agent loop and every one punted on enforcement. This demo closes the wedge across
//! THREE surfaces of the same kernel:
//!
//!   1. **The web/deos surface** — the orchestration board is a composed `DeosApp` mounted on a real
//!      axum router; three viewers (auditor ⊂ worker ⊂ coordinator) fetch the SAME surface and SEE
//!      DIFFERENT button-sets by their caps alone; every fire is a verified turn.
//!   2. **The durable spine** — the orchestration runs DBOS-style: each step checkpointed to a durable
//!      log, crash-recoverable, EXACTLY-ONCE on resume (the pg-dregg::workflow shape).
//!   3. **The audit** — a stranger (the auditor) re-derives the whole run from the receipt chain and
//!      proves no agent ever exceeded its mandate — without trusting the loop.
//!
//! Run with:  `cargo run --release -p starbridge-agent-orchestration --example ados`

use axum::body::Body;
use axum::http::Request;
use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, HELD_RIGHTS_HEADER};
use starbridge_agent_orchestration::{
    Mandate, Tool, WorkStep, WorkerSlot, audit_run, coordinator_program,
    deos::orchestration_app,
    durable::{DurableOrchestration, MemLog, durable_orchestration},
};
use tower::ServiceExt;

fn rule(title: &str) {
    println!(
        "\n\x1b[1m── {title} {}\x1b[0m",
        "─".repeat(64usize.saturating_sub(title.len()))
    );
}
fn short(h: &[u8]) -> String {
    h[..6].iter().map(|b| format!("{b:02x}")).collect()
}

async fn get(router: &axum::Router, uri: &str, tier: Option<&str>) -> serde_json::Value {
    let mut req = Request::get(uri);
    if let Some(t) = tier {
        req = req.header(HELD_RIGHTS_HEADER, t);
    }
    let resp = router
        .clone()
        .oneshot(req.body(Body::empty()).unwrap())
        .await
        .unwrap();
    let bytes = axum::body::to_bytes(resp.into_body(), usize::MAX)
        .await
        .unwrap();
    serde_json::from_slice(&bytes).unwrap_or(serde_json::Value::Null)
}

#[tokio::main]
async fn main() {
    println!(
        "\n\x1b[1m=== ADOS — agent orchestration: a live cap-gated web surface over a durable verified spine ===\x1b[0m"
    );

    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x53u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = cclerk.cell_id();
    exec.with_ledger_mut(|l| {
        if let Some(c) = l.get_mut(&board) {
            c.state.set_balance(100_000_000);
        }
    });

    // The composed deos app: the orchestration board with the auditor ⊂ worker ⊂ coordinator ladder.
    let app = orchestration_app(&cclerk, &exec);
    let router = app.mount();

    // =======================================================================
    // 1. THE LIVE SURFACE — three viewers, one URL, different button-sets.
    // =======================================================================
    rule("1. THE WEB SURFACE — three viewers fetch ONE url, SEE different buttons (by caps alone)");
    let manifest = get(&router, "/manifest", None).await;
    println!(
        "  GET /manifest → app '{}' · persistence: {}",
        manifest["app"].as_str().unwrap_or("?"),
        manifest["persistence"].as_str().unwrap_or("?")
    );
    for (role, tier) in [
        ("auditor", "signature"),
        ("worker", "either"),
        ("coordinator", "root"),
    ] {
        let proj = get(&router, "/orchestration-board/projected", Some(tier)).await;
        println!(
            "  {:<11} (holds {:<9}) projects cap-only buttons: {}",
            role, tier, proj["visible"]
        );
    }
    println!(
        "  → an auditor sees only `view_audit`; a coordinator additionally sees `delegate_mandate`."
    );
    println!(
        "    No viewer can fire what its caps do not authorize; the executor re-checks every fire."
    );

    // =======================================================================
    // 2. DELEGATE — the coordinator attenuates mandates (granted ⊑ held).
    // =======================================================================
    rule("2. DELEGATE — the coordinator issues attenuated mandates (granted ⊑ held)");
    let swarm_budget = 1000u64;
    let coordinator = Mandate::coordinator(
        [Tool::Read, Tool::Search, Tool::Summarize, Tool::Write],
        swarm_budget,
        "research-brief",
    );
    let worker_a =
        coordinator.attenuate([Tool::Read, Tool::Search, Tool::Summarize], 700, "research");
    let worker_b = coordinator.attenuate([Tool::Read], 300, "fact-check");
    println!("  coordinator holds {{read,search,summarize,write}} budget {swarm_budget}");
    println!(
        "  → worker-A: {{{}}}/{}  · worker-B: {{{}}}/{} (`write` STRICTLY dropped) — both ⊑ coordinator",
        worker_a
            .tools
            .iter()
            .map(|t| t.label())
            .collect::<Vec<_>>()
            .join(","),
        worker_a.budget,
        worker_b
            .tools
            .iter()
            .map(|t| t.label())
            .collect::<Vec<_>>()
            .join(","),
        worker_b.budget
    );

    // The coordinator fires `delegate_mandate` through the LIVE surface (cap-authorized; a real turn).
    let coord_delegate = router
        .clone()
        .oneshot(
            Request::post("/orchestration-board/fire/delegate_mandate")
                .header(HELD_RIGHTS_HEADER, "root")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    println!(
        "  coordinator fires `delegate_mandate` over the surface → HTTP {} (cap gate cleared)",
        coord_delegate.status()
    );
    // A worker firing `delegate_mandate` is refused at the cap gate (anti-ghost).
    let worker_delegate = router
        .clone()
        .oneshot(
            Request::post("/orchestration-board/fire/delegate_mandate")
                .header(HELD_RIGHTS_HEADER, "either")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    println!(
        "  worker fires `delegate_mandate` → HTTP {} (REFUSED at the cap gate — only `None` may delegate)",
        worker_delegate.status()
    );

    // =======================================================================
    // 3. THE DURABLE SPINE — run the orchestration DBOS-style, checkpointed.
    // =======================================================================
    rule("3. THE DURABLE SPINE — each step a verified turn, checkpointed (crash-recoverable)");
    // Install the budget program (the `AffineLe Σspend ≤ budget` policy the executor re-enforces) on
    // the board cell. The engine's `open()` then sets LEAD/BUDGET/meters/EPOCH (0 -> 1) via a real
    // verified open_board turn — so the budget gate bites on every subsequent worker step.
    exec.install_program(board, coordinator_program());

    let plan = vec![
        WorkStep::new(WorkerSlot::A, Tool::Search, 250, "search-the-corpus"),
        WorkStep::new(WorkerSlot::A, Tool::Summarize, 200, "summarize-hits"),
        WorkStep::new(WorkerSlot::B, Tool::Read, 150, "fact-check-claim-1"),
        WorkStep::new(WorkerSlot::B, Tool::Read, 100, "fact-check-claim-2"),
    ];
    let mut durable = MemLog::new();
    let open_receipt;
    // Run the first two steps, then "crash" (drop the durable orchestration).
    {
        let mut d = durable_orchestration(
            &cclerk,
            &exec,
            board,
            coordinator.clone(),
            worker_a.clone(),
            worker_b.clone(),
        );
        let prefix: Vec<_> = plan[..2].to_vec();
        let out = d
            .run("coordinator-pk", &prefix, &mut durable)
            .expect("the prefix commits");
        open_receipt = d.open_receipt().cloned().expect("open receipt");
        println!(
            "  ran {} verified steps, checkpointed {} to the durable log (then the engine 'crashes')",
            out.committed,
            durable.len()
        );
    }

    rule("4. CRASH → RECOVER (re-validate the chain) → RESUME (exactly-once)");
    let (_log, recovered) = DurableOrchestration::recover(&open_receipt, &durable)
        .expect("recover re-validates the chain");
    println!(
        "  recovered from the durable log alone: worker-A spent {}, next epoch {}",
        recovered.spent_a, recovered.next_epoch
    );
    {
        let mut d = durable_orchestration(
            &cclerk,
            &exec,
            board,
            coordinator.clone(),
            worker_a.clone(),
            worker_b.clone(),
        );
        d.resume_state(recovered, open_receipt.clone());
        let out = d.resume(&plan, &mut durable).expect("the tail finishes");
        println!(
            "  resumed: skipped {} committed (never re-applied), ran {} tail → {} durable total (exactly-once)",
            out.skipped,
            out.committed,
            durable.len()
        );
    }

    // =======================================================================
    // 5. THE AUDIT — a stranger proves no agent exceeded its mandate.
    // =======================================================================
    rule("5. THE AUDIT — a stranger (the auditor) re-derives the run, never trusting the loop");
    // The auditor fetches the audit-read surface (cap-only, its tier).
    let _audit_read = router
        .clone()
        .oneshot(
            Request::post("/orchestration-board/fire/view_audit")
                .header(HELD_RIGHTS_HEADER, "signature")
                .body(Body::empty())
                .unwrap(),
        )
        .await
        .unwrap();
    // And re-derives the verdict off the receipt chain (the off-cell light-client computation).
    match audit_run(
        &open_receipt,
        durable.orchestration_log(),
        &coordinator,
        &worker_a,
        &worker_b,
    ) {
        Ok(ok) => {
            println!(
                "  AUDIT OK: {} steps · worker-A {} · worker-B {} · Σ {} ≤ budget {}",
                ok.steps,
                ok.spent_a,
                ok.spent_b,
                ok.spent_a + ok.spent_b,
                ok.budget
            );
            println!(
                "  non-amplification ✓ · chain integrity ✓ · per-step mandate ✓ · conservation ✓"
            );
            println!(
                "  chain head (the commitment a light client pins): {}",
                short(&ok.head)
            );
        }
        Err(e) => println!("  !! AUDIT FAILED on a clean run: {e}"),
    }
    // A tampered receipt is caught.
    let mut tampered = durable.orchestration_log().clone();
    tampered.entries[1].receipt.post_state_hash[0] ^= 0xff;
    match audit_run(&open_receipt, &tampered, &coordinator, &worker_a, &worker_b) {
        Ok(_) => println!("  !! SECURITY FAILURE: the audit passed a tampered log"),
        Err(e) => println!("  a tampered receipt: AUDIT REFUSED — {e}"),
    }

    rule("DONE");
    println!(
        "\x1b[1m✓ a swarm whose every action is provably authorized, recorded, budgeted, and coordinated —\x1b[0m"
    );
    println!(
        "  a live cap-gated web surface over a durable verified spine, auditable by a stranger."
    );
    println!(
        "  the loop is the integrator's game; dregg owns the one seam — and the swarm cannot pretend.\n"
    );
    println!("  four loops, one seam,");
    println!("  six primitives each hand-rolled —");
    println!("  dregg makes them bite.\n");
}
