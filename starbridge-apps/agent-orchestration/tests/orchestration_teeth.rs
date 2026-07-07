//! Integration teeth for the DURABLE + AUDITABLE agent orchestration — every claim a real
//! executor turn or a real audit, never a mock.
//!
//! The teeth, in both polarities:
//!   * an honest orchestration RUNS through the verified executor + AUDITS clean;
//!   * a worker that exceeds its mandate (wider tool / over sub-budget) is REFUSED in the fire path
//!     ([`OrchestrationError::OutOfMandate`]) — fail-closed, before submission;
//!   * the executor's `AffineLe` swarm-budget gate REFUSES an over-swarm-budget step (the real,
//!     in-the-kernel tooth) — the durable log is unmoved;
//!   * a TAMPERED receipt breaks the audit chain ([`AuditError::ChainBroken`]);
//!   * an AMPLIFIED worker mandate is caught by the audit ([`AuditError::AmplifiedMandate`]);
//!   * CRASH → RECOVER → RESUME is exactly-once (the committed prefix is skipped, never re-applied).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, EmbeddedExecutor,
};
use dregg_cell::FactoryCreationParams;
use starbridge_agent_orchestration::{
    AuditError, Mandate, ORCHESTRATION_FACTORY_VK, OrchestrationEngine, OrchestrationError,
    OrchestrationLog, Tool, WorkStep, WorkerSlot, audit_run, coordinator_child_program_vk,
    orchestration_factory_descriptor, recover,
};

/// Build a born coordinator board cell driven by `cclerk`/`exec`, returning its CellId. Mirrors the
/// proven swarm-orchestration / supply-chain factory-birth pattern.
fn born_board(cclerk: &AppCipherclerk, exec: &EmbeddedExecutor, seed: &[u8]) -> CellId {
    exec.deploy_factory(orchestration_factory_descriptor());
    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|l| {
        if let Some(c) = l.get_mut(&agent) {
            c.state.set_balance(100_000_000);
        }
    });
    let owner = cclerk.public_key().0;
    let token = *blake3::hash(seed).as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(coordinator_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(ORCHESTRATION_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth).expect("board birth commits");
    let board = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|l| {
        if let Some(a) = l.get_mut(&agent) {
            a.capabilities.grant(board, AuthRequired::Signature);
        }
    });
    board
}

fn mandates() -> (Mandate, Mandate, Mandate) {
    let coordinator = Mandate::coordinator(
        [Tool::Read, Tool::Search, Tool::Summarize, Tool::Write],
        1000,
        "task",
    );
    let a = coordinator.attenuate([Tool::Read, Tool::Search, Tool::Summarize], 700, "research");
    let b = coordinator.attenuate([Tool::Read], 300, "fact-check");
    (coordinator, a, b)
}

#[test]
fn honest_orchestration_runs_and_audits_clean() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"honest");
    let (coord, a, b) = mandates();

    let plan = vec![
        WorkStep::new(WorkerSlot::A, Tool::Search, 250, "search"),
        WorkStep::new(WorkerSlot::A, Tool::Summarize, 200, "summarize"),
        WorkStep::new(WorkerSlot::B, Tool::Read, 150, "fact-check"),
    ];
    let mut log = OrchestrationLog::new();
    let open_receipt;
    {
        let mut engine =
            OrchestrationEngine::new(&cclerk, &exec, board, coord.clone(), a.clone(), b.clone());
        let committed = engine
            .run("lead", &plan, &mut log)
            .expect("the run commits");
        assert_eq!(committed, 3, "all three steps committed");
        open_receipt = engine.open_receipt().cloned().expect("open receipt");
        assert_eq!(engine.spent(WorkerSlot::A), 450);
        assert_eq!(engine.spent(WorkerSlot::B), 150);
    }
    assert_eq!(log.len(), 3, "three verified turns checkpointed");

    // AUDIT: a light client re-derives the run and proves no agent exceeded its mandate.
    let ok = audit_run(&open_receipt, &log, &coord, &a, &b).expect("clean run audits OK");
    assert_eq!(ok.steps, 3);
    assert_eq!(ok.spent_a, 450);
    assert_eq!(ok.spent_b, 150);
    assert!(ok.spent_a + ok.spent_b <= ok.budget, "Σ spend ≤ budget");
}

#[test]
fn over_tool_worker_step_is_refused_in_the_fire_path() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x22u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"over-tool");
    let (coord, a, b) = mandates();

    let mut log = OrchestrationLog::new();
    let mut engine = OrchestrationEngine::new(&cclerk, &exec, board, coord, a, b);
    engine.open("lead").expect("opens");

    // worker-B reaches for `write` — a tool NOT in its mandate (read only). REFUSED before submission.
    let over = WorkStep::new(WorkerSlot::B, Tool::Write, 10, "exfiltrate");
    let err = engine
        .step(&over, &mut log)
        .expect_err("over-tool step must be refused");
    assert!(
        matches!(
            err,
            OrchestrationError::OutOfMandate {
                worker: WorkerSlot::B,
                tool: Tool::Write,
                ..
            }
        ),
        "expected OutOfMandate(write), got {err:?}"
    );
    assert!(
        log.is_empty(),
        "a refused step checkpoints nothing — fail-closed"
    );
}

#[test]
fn over_subbudget_worker_step_is_refused() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x23u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"over-subbudget");
    let (coord, a, b) = mandates();

    let mut log = OrchestrationLog::new();
    let mut engine = OrchestrationEngine::new(&cclerk, &exec, board, coord, a, b);
    engine.open("lead").expect("opens");

    // worker-B has a 300 sub-budget. Spend 200 (fits), then 200 more would breach 300.
    engine
        .step(
            &WorkStep::new(WorkerSlot::B, Tool::Read, 200, "read-1"),
            &mut log,
        )
        .expect("first read fits the sub-budget");
    let err = engine
        .step(
            &WorkStep::new(WorkerSlot::B, Tool::Read, 200, "read-2"),
            &mut log,
        )
        .expect_err("over-sub-budget step must be refused");
    assert!(
        matches!(
            err,
            OrchestrationError::OutOfMandate {
                worker: WorkerSlot::B,
                ..
            }
        ),
        "expected OutOfMandate(budget), got {err:?}"
    );
    assert_eq!(log.len(), 1, "only the in-budget step checkpointed");
}

#[test]
fn executor_affine_gate_refuses_an_over_swarm_budget_step() {
    // The REAL in-kernel tooth: even if a worker's sub-budget would allow it, the coordinator's
    // CellProgram `AffineLe` gate refuses Σ worker spend > swarm budget. We set up the swarm budget
    // so worker-A's full sub-budget + worker-B's would breach the SWARM mandate, and drive a step that
    // passes the off-ledger pre-check (its own sub-budget) but breaches the affine sum on-ledger.
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x24u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"affine-gate");

    // Coordinator swarm budget 500; each worker GRANTED a 500 sub-budget (each ⊑ on tools+budget),
    // but together they cannot exceed 500 — the affine sum is the binding constraint.
    let coord = Mandate::coordinator([Tool::Read, Tool::Search], 500, "task");
    let a = coord.attenuate([Tool::Read, Tool::Search], 500, "a");
    let b = coord.attenuate([Tool::Read], 500, "b");

    let mut log = OrchestrationLog::new();
    let mut engine = OrchestrationEngine::new(&cclerk, &exec, board, coord, a, b);
    engine.open("lead").expect("opens");

    // worker-A spends 400 (within its 500 sub-budget AND the 500 swarm budget).
    engine
        .step(
            &WorkStep::new(WorkerSlot::A, Tool::Search, 400, "a-search"),
            &mut log,
        )
        .expect("A's 400 fits both budgets");
    // worker-B spends 200: within ITS 500 sub-budget (off-ledger pre-check passes), but 400+200=600 >
    // 500 swarm budget — the executor's AffineLe gate REFUSES it on commit.
    let err = engine
        .step(
            &WorkStep::new(WorkerSlot::B, Tool::Read, 200, "b-read"),
            &mut log,
        )
        .expect_err("the affine swarm-budget gate must refuse");
    assert!(
        matches!(err, OrchestrationError::Refused(_)),
        "expected an executor Refused (AffineLe gate), got {err:?}"
    );
    assert_eq!(
        log.len(),
        1,
        "the refused step checkpointed nothing — fail-closed"
    );
}

#[test]
fn audit_catches_a_tampered_receipt() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x33u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"tamper");
    let (coord, a, b) = mandates();

    let plan = vec![
        WorkStep::new(WorkerSlot::A, Tool::Search, 250, "s"),
        WorkStep::new(WorkerSlot::B, Tool::Read, 150, "r"),
    ];
    let mut log = OrchestrationLog::new();
    let open_receipt;
    {
        let mut engine =
            OrchestrationEngine::new(&cclerk, &exec, board, coord.clone(), a.clone(), b.clone());
        engine.run("lead", &plan, &mut log).expect("runs");
        open_receipt = engine.open_receipt().cloned().unwrap();
    }
    // The clean log audits.
    assert!(audit_run(&open_receipt, &log, &coord, &a, &b).is_ok());

    // Flip a byte in a logged receipt's post-state — the chain no longer links.
    let mut tampered = log.clone();
    tampered.entries[0].receipt.post_state_hash[0] ^= 0xff;
    let err = audit_run(&open_receipt, &tampered, &coord, &a, &b)
        .expect_err("a tampered receipt must break the audit");
    assert!(
        matches!(err, AuditError::ChainBroken(_)),
        "expected ChainBroken, got {err:?}"
    );

    // STEP↔RECEIPT CONTENT: tamper the STEP RECORD (not the receipt) — the chain still links and the
    // tool stays in scope, but the recorded step no longer matches the authentic turn the receipt
    // commits (`turn.hash() == turn_hash` holds, but the turn's effects don't bind this sub_task). The
    // mandate + chain checks would trust it on faith; the content cross-check catches it.
    let mut forged = log.clone();
    forged.entries[0].step.sub_task = "FORGED".to_string();
    let err = audit_run(&open_receipt, &forged, &coord, &a, &b)
        .expect_err("a step record disagreeing with its receipt's turn must be caught");
    assert!(
        matches!(err, AuditError::StepNotFaithful { ordinal: 0 }),
        "expected StepNotFaithful, got {err:?}"
    );
}

#[test]
fn audit_catches_an_amplified_mandate() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x34u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"amplified");
    let (coord, a, b) = mandates();

    let plan = vec![WorkStep::new(WorkerSlot::A, Tool::Search, 250, "s")];
    let mut log = OrchestrationLog::new();
    let open_receipt;
    {
        let mut engine =
            OrchestrationEngine::new(&cclerk, &exec, board, coord.clone(), a.clone(), b.clone());
        engine.run("lead", &plan, &mut log).expect("runs");
        open_receipt = engine.open_receipt().cloned().unwrap();
    }
    // Audit the clean log against an AMPLIFIED worker-A mandate (claims `spend`, more budget).
    let amplified = Mandate::coordinator(
        [Tool::Read, Tool::Search, Tool::Summarize, Tool::Spend],
        9999,
        "amplified",
    );
    let err = audit_run(&open_receipt, &log, &coord, &amplified, &b)
        .expect_err("an amplified mandate must be caught");
    assert!(
        matches!(
            err,
            AuditError::AmplifiedMandate {
                worker: WorkerSlot::A
            }
        ),
        "expected AmplifiedMandate(A), got {err:?}"
    );
}

#[test]
fn crash_recover_resume_is_exactly_once() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x44u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"exactly-once");
    let (coord, a, b) = mandates();

    let plan = vec![
        WorkStep::new(WorkerSlot::A, Tool::Search, 250, "s1"),
        WorkStep::new(WorkerSlot::A, Tool::Summarize, 200, "s2"),
        WorkStep::new(WorkerSlot::B, Tool::Read, 150, "r1"),
        WorkStep::new(WorkerSlot::B, Tool::Read, 100, "r2"),
    ];
    let mut log = OrchestrationLog::new();
    let open_receipt;

    // Run the first two steps, then "crash" (drop the engine).
    {
        let mut engine =
            OrchestrationEngine::new(&cclerk, &exec, board, coord.clone(), a.clone(), b.clone());
        engine.open("lead").expect("opens");
        open_receipt = engine.open_receipt().cloned().unwrap();
        for step in &plan[..2] {
            engine.step(step, &mut log).expect("prefix commits");
        }
        assert_eq!(log.len(), 2);
    }

    // Recover from the log alone — re-validate the chain, re-derive the resumable state.
    let recovered = recover(&open_receipt, &log).expect("recovery re-validates the chain");
    assert_eq!(recovered.spent_a, 450);
    assert_eq!(recovered.spent_b, 0);

    // Resume the SAME plan — the committed prefix is skipped, only the tail runs.
    {
        let mut engine =
            OrchestrationEngine::new(&cclerk, &exec, board, coord.clone(), a.clone(), b.clone());
        engine.resume_state(recovered, open_receipt.clone());
        let (skipped, committed) = engine.resume(&plan, &mut log).expect("the tail finishes");
        assert_eq!(
            skipped, 2,
            "the committed prefix is skipped, never re-applied"
        );
        assert_eq!(committed, 2, "only the uncommitted tail runs");
    }
    assert_eq!(
        log.len(),
        4,
        "four turns total — no double-apply (exactly-once)"
    );

    // The whole run audits clean.
    let ok = audit_run(&open_receipt, &log, &coord, &a, &b).expect("the resumed run audits");
    assert_eq!(ok.steps, 4);
    assert_eq!(ok.spent_a, 450);
    assert_eq!(ok.spent_b, 250);
}

#[test]
fn recover_refuses_a_tampered_log_closed() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x55u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let board = born_board(&cclerk, &exec, b"recover-tamper");
    let (coord, a, b) = mandates();

    let plan = vec![
        WorkStep::new(WorkerSlot::A, Tool::Search, 250, "s"),
        WorkStep::new(WorkerSlot::B, Tool::Read, 150, "r"),
    ];
    let mut log = OrchestrationLog::new();
    let open_receipt;
    {
        let mut engine = OrchestrationEngine::new(&cclerk, &exec, board, coord, a, b);
        engine.run("lead", &plan, &mut log).expect("runs");
        open_receipt = engine.open_receipt().cloned().unwrap();
    }
    // Substitute a persisted receipt's previous hash — the chain no longer links.
    let mut tampered = log.clone();
    tampered.entries[1].receipt.previous_receipt_hash = Some([0x99u8; 32]);
    let err =
        recover(&open_receipt, &tampered).expect_err("recovery of a tampered log must refuse");
    assert!(
        matches!(err, AuditError::ChainBroken(_)),
        "expected ChainBroken on recovery, got {err:?}"
    );
}
