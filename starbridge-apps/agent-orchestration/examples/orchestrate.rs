//! # Verifiable DURABLE + AUDITABLE agent orchestration — the runnable demo.
//!
//! A stranger runs this and WATCHES accountability fire, never trusting the loops. A COORDINATOR holds
//! a task and a swarm budget; it issues two WORKERS each an ATTENUATED MANDATE (a narrowed tool-set ∧ a
//! sub-budget — `granted ⊑ held`, the proven non-amplification); every worker action is a cap-gated
//! VERIFIED TURN through the real embedded executor, checkpointed to a durable receipt log; and the
//! whole run is AUDITABLE — a light client re-derives it from the receipt chain and proves no agent
//! ever exceeded its mandate.
//!
//!   1. **OPEN** the dispatch board — a factory-born COORDINATOR cell whose installed program IS the
//!      swarm budget policy, born through the REAL verified executor.
//!   2. **DELEGATE** — the coordinator attenuates its broad mandate into two worker mandates (each
//!      strictly weaker: `granted ⊑ held`); worker-B's `write` tool is DROPPED (strict attenuation).
//!   3. **RUN** the orchestration — a 4-step plan (worker-A searches + summarizes, worker-B fact-checks
//!      twice); we run the first two now, "crash", then resume the rest. Each step a verified turn
//!      CHECKPOINTED to the durable log.
//!   4. **REFUSE the over-mandate** — worker-B reaches for `write` (a tool NOT in its mandate) and
//!      worker-A tries to over-spend its sub-budget: both REFUSED, fail-closed, in the fire path
//!      (before submission). The durable log is unmoved. (The executor's `AffineLe` swarm-budget gate —
//!      the real in-kernel tooth — is exercised by `tests/orchestration_teeth.rs`.)
//!   5. **CRASH + RECOVER + RESUME (exactly-once)** — drop the engine; rebuild from the durable log
//!      alone (re-validating the receipt chain on the way up); resume the SAME plan — the committed
//!      prefix is SKIPPED, never re-applied.
//!   6. **AUDIT clean** — the auditor re-derives the whole run from the receipt chain and proves no
//!      agent exceeded its mandate (non-amplification + chain integrity + per-step mandate + budget).
//!   7. **AUDIT catches tamper** — a single byte flipped in a logged receipt breaks the chain; the
//!      audit refuses CLOSED. And an audit against an AMPLIFIED mandate is refused.
//!
//! Every frame is a real turn through the embedded verified executor (or a real static check), not a
//! mock. Run with:  `cargo run --release -p starbridge-agent-orchestration --example orchestrate`

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellMode, EmbeddedExecutor,
};
use dregg_cell::FactoryCreationParams;
use starbridge_agent_orchestration::{
    AuditError, Mandate, OrchestrationEngine, OrchestrationError, OrchestrationLog, Tool, WorkStep,
    WorkerSlot, audit_run, coordinator_child_program_vk, orchestration_factory_descriptor, recover,
};

fn short(h: &[u8]) -> String {
    h[..6].iter().map(|b| format!("{b:02x}")).collect()
}

fn rule(title: &str) {
    println!(
        "\n\x1b[1m── {title} {}\x1b[0m",
        "─".repeat(62usize.saturating_sub(title.len()))
    );
}

fn main() {
    println!(
        "\n\x1b[1m=== Verifiable DURABLE + AUDITABLE agent orchestration — every action a verified turn ===\x1b[0m"
    );

    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x53u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");

    // ── BIRTH the coordinator dispatch-board cell through the real executor ──
    exec.deploy_factory(orchestration_factory_descriptor());
    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|l| {
        if let Some(c) = l.get_mut(&agent) {
            c.state.set_balance(100_000_000);
        }
    });
    let owner = cclerk.public_key().0;
    let token = *blake3::hash(b"agent-orchestration-demo").as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(coordinator_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth =
        cclerk.create_from_factory(*b"starbridge-agent-orchestr-factry", owner, token, params);
    let birth_r = exec.submit_turn(&birth).expect("board birth commits");
    let board = dregg_app_framework::CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|l| {
        if let Some(a) = l.get_mut(&agent) {
            a.capabilities.grant(board, AuthRequired::Signature);
        }
    });

    rule("1. OPEN the dispatch board (factory-born COORDINATOR)");
    println!(
        "  board cell {} · birth receipt {}",
        short(board.as_bytes()),
        short(&birth_r.receipt_hash())
    );
    println!(
        "  its installed program IS the swarm budget policy (AffineLe Σspend ≤ budget · WriteOnce · no-replay)"
    );

    // =======================================================================
    // 2. DELEGATE — the coordinator attenuates its broad mandate into two
    //    worker mandates (each strictly weaker: granted ⊑ held).
    // =======================================================================
    rule("2. DELEGATE — attenuated mandates (granted ⊑ held, the proven non-amplification)");
    let swarm_budget = 1000u64;
    // The coordinator HOLDS read+search+summarize+write, the whole budget, the top task.
    let coordinator = Mandate::coordinator(
        [Tool::Read, Tool::Search, Tool::Summarize, Tool::Write],
        swarm_budget,
        "research-and-write-a-brief",
    );
    // Worker-A: a researcher — read+search+summarize, a 700 sub-budget. (write DROPPED.)
    let worker_a_mandate =
        coordinator.attenuate([Tool::Read, Tool::Search, Tool::Summarize], 700, "research");
    // Worker-B: a reader — read only, a 300 sub-budget. (search/summarize/write DROPPED.)
    let worker_b_mandate = coordinator.attenuate([Tool::Read], 300, "fact-check");
    assert!(worker_a_mandate.le(&coordinator), "A ⊑ coordinator");
    assert!(worker_b_mandate.le(&coordinator), "B ⊑ coordinator");
    assert!(
        !worker_b_mandate.tools.contains(&Tool::Write),
        "STRICT: B's mandate dropped `write`"
    );
    println!("  coordinator holds {{read,search,summarize,write}} budget {swarm_budget}");
    println!(
        "  → worker-A mandate: {{{}}} sub-budget {}   (⊑ coordinator)",
        worker_a_mandate
            .tools
            .iter()
            .map(|t| t.label())
            .collect::<Vec<_>>()
            .join(","),
        worker_a_mandate.budget
    );
    println!(
        "  → worker-B mandate: {{{}}} sub-budget {}   (⊑ coordinator; `write` STRICTLY dropped)",
        worker_b_mandate
            .tools
            .iter()
            .map(|t| t.label())
            .collect::<Vec<_>>()
            .join(","),
        worker_b_mandate.budget
    );

    // =======================================================================
    // 3. RUN the orchestration — each step a verified turn checkpointed.
    // =======================================================================
    rule("3. RUN — each worker step a VERIFIED TURN, checkpointed to the durable log");
    // The full plan (4 steps; we run the first 2 now, "crash", then resume the rest).
    let plan = vec![
        WorkStep::new(WorkerSlot::A, Tool::Search, 250, "search-the-corpus"),
        WorkStep::new(WorkerSlot::A, Tool::Summarize, 200, "summarize-hits"),
        WorkStep::new(WorkerSlot::B, Tool::Read, 150, "fact-check-claim-1"),
        WorkStep::new(WorkerSlot::B, Tool::Read, 100, "fact-check-claim-2"),
    ];

    let mut log = OrchestrationLog::new();
    let open_receipt;
    {
        let mut engine = OrchestrationEngine::new(
            &cclerk,
            &exec,
            board,
            coordinator.clone(),
            worker_a_mandate.clone(),
            worker_b_mandate.clone(),
        );
        engine.open("coordinator-pk").expect("board opens");
        open_receipt = engine.open_receipt().cloned().expect("open receipt");

        // Run the first TWO steps (the prefix), then "crash" (drop the engine).
        for step in &plan[..2] {
            let r = engine
                .step(step, &mut log)
                .expect("verified worker step commits");
            println!(
                "  {} {} ({}) cost {} → receipt {} · running spend {}",
                step.worker.label(),
                step.tool.label(),
                step.sub_task,
                step.cost,
                short(&r.receipt_hash()),
                engine.spent(step.worker)
            );
        }
        println!(
            "  checkpointed {} verified turns to the durable log (the receipt chain)",
            log.len()
        );

        // =======================================================================
        // 4. REFUSE the over-mandate (in the fire path) + the over-budget (executor).
        // =======================================================================
        rule("4. REFUSE the over-mandate — fail-closed, in the fire path");
        // (a) worker-B reaches for `write` — a tool NOT in its mandate.
        let over_tool = WorkStep::new(WorkerSlot::B, Tool::Write, 10, "exfiltrate");
        match engine.step(&over_tool, &mut log) {
            Ok(_) => println!("  !! UNEXPECTEDLY COMMITTED — the scope tooth did not fire"),
            Err(OrchestrationError::OutOfMandate { why, .. }) => {
                println!("  (a) worker-B tries tool `write`: REFUSED before submission — {why}")
            }
            Err(e) => println!("  (a) worker-B `write`: REFUSED — {e}"),
        }
        // (b) worker-A (running spend 450, sub-budget 700) tries to spend 300 more — 450+300=750 >
        //     700: over its sub-budget. A pure single-step refusal (nothing commits to the log).
        let over_budget = WorkStep::new(WorkerSlot::A, Tool::Summarize, 300, "over-budget-summary");
        match engine.step(&over_budget, &mut log) {
            Ok(_) => println!("  !! UNEXPECTEDLY COMMITTED — the budget tooth did not fire"),
            Err(OrchestrationError::OutOfMandate { why, .. }) => {
                println!("  (b) worker-A tries to over-spend its sub-budget: REFUSED — {why}")
            }
            Err(e) => println!("  (b) worker-A over-spend: REFUSED — {e}"),
        }
        println!(
            "  fail-closed: the durable log still holds exactly {} committed steps, unmoved by the refusals",
            log.len()
        );
        // engine dropped HERE — the in-process engine state is gone; `log` + `open_receipt` survive.
    }

    // =======================================================================
    // 5. CRASH + RECOVER + RESUME (exactly-once).
    // =======================================================================
    rule("5. CRASH → RECOVER (re-validate the chain) → RESUME (exactly-once)");
    let committed_at_crash = log.len();
    println!(
        "  engine dropped; the durable log survives with {committed_at_crash} committed steps"
    );
    // Recover: re-validate the receipt chain from the log ALONE, re-derive the resumable state.
    let recovered =
        recover(&open_receipt, &log).expect("the durable chain re-validates on recovery");
    println!(
        "  recovered from the log: worker-A spent {}, worker-B spent {}, next epoch {}",
        recovered.spent_a, recovered.spent_b, recovered.next_epoch
    );
    // Resume the SAME full plan — the committed prefix is skipped, only the tail runs.
    {
        let mut engine = OrchestrationEngine::new(
            &cclerk,
            &exec,
            board,
            coordinator.clone(),
            worker_a_mandate.clone(),
            worker_b_mandate.clone(),
        );
        engine.resume_state(recovered, open_receipt.clone());
        let (skipped, committed) = engine.resume(&plan, &mut log).expect("the tail finishes");
        println!(
            "  resumed: skipped {skipped} committed steps (never re-applied), ran {committed} tail steps"
        );
        assert_eq!(
            log.len(),
            plan.len(),
            "every plan step is now durable — no double-apply"
        );
    }

    // =======================================================================
    // 6. AUDIT clean — a light client proves no agent exceeded its mandate.
    // =======================================================================
    rule("6. AUDIT — a light client proves no agent ever exceeded its mandate");
    match audit_run(
        &open_receipt,
        &log,
        &coordinator,
        &worker_a_mandate,
        &worker_b_mandate,
    ) {
        Ok(ok) => {
            println!(
                "  AUDIT OK: {} steps · worker-A spent {} · worker-B spent {} · Σ {} ≤ budget {}",
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

    // =======================================================================
    // 7. AUDIT catches tamper + an amplified mandate.
    // =======================================================================
    rule("7. AUDIT catches a TAMPERED receipt + an AMPLIFIED mandate");
    // (a) Flip a byte in a logged receipt's post-state — the chain no longer links.
    let mut tampered = log.clone();
    tampered.entries[1].receipt.post_state_hash[0] ^= 0xff;
    match audit_run(
        &open_receipt,
        &tampered,
        &coordinator,
        &worker_a_mandate,
        &worker_b_mandate,
    ) {
        Ok(_) => println!("  !! SECURITY FAILURE: the audit passed a tampered log"),
        Err(AuditError::ChainBroken(_)) => {
            println!("  (a) one byte flipped in a logged receipt: AUDIT REFUSED (chain broken)")
        }
        Err(e) => println!("  (a) tampered log: AUDIT REFUSED — {e}"),
    }
    // (b) Audit the SAME clean log but against an AMPLIFIED worker mandate (claims `spend`, more budget).
    let amplified = Mandate::coordinator(
        [Tool::Read, Tool::Search, Tool::Summarize, Tool::Spend],
        9999,
        "amplified",
    );
    match audit_run(
        &open_receipt,
        &log,
        &coordinator,
        &amplified,
        &worker_b_mandate,
    ) {
        Ok(_) => println!("  !! SECURITY FAILURE: the audit passed an amplified mandate"),
        Err(AuditError::AmplifiedMandate { worker }) => println!(
            "  (b) a worker mandate NOT ⊑ the coordinator's: AUDIT REFUSED (amplified: {})",
            worker.label()
        ),
        Err(e) => println!("  (b) amplified mandate: AUDIT REFUSED — {e}"),
    }

    rule("DONE");
    println!(
        "\x1b[1m✓ a durable, exactly-once, auditable multi-agent orchestration where every step is a verified turn,\x1b[0m"
    );
    println!(
        "  bounded by an attenuated mandate (granted ⊑ held), and a light client is never fooled.\n"
    );
    println!("  three small lies a worker might tell —");
    println!("  i was scoped, i was budgeted, i did —");
    println!("  three checks the audit re-derives from the chain;");
    println!("  the orchestration cannot pretend.\n");
}
