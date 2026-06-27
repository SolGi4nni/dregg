//! # The orchestration as a pg-dregg-shaped DURABLE WORKFLOW — DBOS, but every step a verified turn.
//!
//! `docs/PG-DREGG.md` + `pg-dregg/src/workflow.rs` (`WorkflowEngine` / `run_durable` /
//! `recover_from_durable` / `resume_durable` / the `RootChain` anti-substitution tooth) +
//! `docs/deos/DURABLE-WORKFLOW.md`. This module re-expresses the agent orchestration ON the
//! pg-dregg durable-workflow SHAPE, so the orchestration is DBOS-style durable execution where every
//! step is unforgeable + attenuable + conserving + receipted — because each step is a VERIFIED TURN
//! over the durable verified state.
//!
//! ## What DBOS gives, and the gap dregg closes
//!
//! [DBOS](https://www.dbos.dev/) gives durable execution: a multi-step workflow checkpoints each step,
//! and after a crash it replays from the log so the workflow runs **exactly once**. Real — but a DBOS
//! step is ordinary code issuing an ordinary `UPDATE`, so DBOS trusts the writer: a worker's buggy or
//! malicious step `spend += 1_000_000` *executes*, and DBOS faithfully makes it execute exactly once.
//! Budget is forged, durably. This is exactly the gap the four ADOS integrators all punted on (their
//! own honest words: "no budget enforcement, a runaway could drain $1000s").
//!
//! [`DurableOrchestration`] drives the SAME durable-execution shape on the verified orchestration spine,
//! where a step is admitted ONLY through the verified-turn gate ([`crate::OrchestrationEngine::step`]):
//! the MANDATE pre-check (scope ∧ sub-budget) + the EXECUTOR (`AffineLe Σspend ≤ budget` + no-replay),
//! then APPLY + LOG. A bare over-mandate write has no way in.
//!
//! ## The bridge to pg-dregg (named, not faked)
//!
//! pg-dregg is a STANDALONE workspace (excluded from the parent `members`; a `cargo-pgrx` cdylib must
//! not join `cargo check --workspace`), so it is the MODEL here, not a dependency. The correspondence
//! is exact and intentional:
//!
//! | pg-dregg `workflow.rs`            | here                                   | the same thing |
//! |----------------------------------|----------------------------------------|----------------|
//! | `WorkflowEngine`                 | [`crate::OrchestrationEngine`]          | the verified-turn step driver |
//! | `Step` / `Workflow`              | [`crate::WorkStep`] / `&[WorkStep]`     | the planned choreography |
//! | `DurableLog` / `MemLog` / commit_log | [`DurableLog`] / [`crate::OrchestrationLog`] | the external sink that outlives a crash |
//! | `run_durable` / `resume_durable` | [`DurableOrchestration::run`] / [`resume`](DurableOrchestration::resume) | checkpoint each verified turn; exactly-once on resume |
//! | `recover_from_durable`           | [`crate::recover`]                      | rebuild from the log, re-validating the chain |
//! | the `RootChain` anti-substitution tooth (`verify_chain_step`) | [`crate::audit_run`]'s pairwise `verify_receipt_extends` | a substituted/reordered batch refused — the SAME "this chains onto the head" question |
//!
//! So a host that has pg-dregg wired (the [`crate::deos::orchestration_app`] advertises
//! [`dregg_app_framework::PersistenceSeam::PgDregg`]) runs this orchestration as durable verified SQL
//! state; the in-process [`crate::OrchestrationLog`] is the same shape the `dregg.commit_log` table holds.
//!
//! ## What is checkpointed, and exactly-once
//!
//! Each committed step's verified [`dregg_turn::TurnReceipt`] is appended to a [`DurableLog`] the instant
//! it commits (one logical commit, as the executor's submit-gate + the append are one unit). A crash
//! leaves exactly the committed prefix durable; [`crate::recover`] rebuilds the resumable state from the
//! log alone (re-validating the chain on the way up); [`DurableOrchestration::resume`] runs only the
//! uncommitted tail — the committed prefix is SKIPPED, never re-applied. Exactly-once holds two ways
//! that agree: the index-skip (fast path) and the executor's no-replay epoch (the backstop — a stale
//! re-submit of a committed step would not strictly advance the epoch and is refused).

use dregg_turn::TurnReceipt;

use crate::{
    AuditError, Mandate, OrchestrationEngine, OrchestrationError, OrchestrationLog, RecoveredState,
    WorkStep, WorkerSlot, recover,
};

/// A **durable sink** that outlives a crash — the in-process analogue of pg-dregg's `DurableLog` /
/// `dregg.commit_log`. An implementation persists each committed step's verified receipt the instant it
/// commits, and can load them back on recovery. The default [`MemLog`] keeps them in memory (the
/// in-process stand-in for the durable table); a host backs this with the real durable store.
pub trait DurableLog {
    /// Append a committed step's verified receipt (one logical durable commit).
    fn append(
        &mut self,
        step: &WorkStep,
        spent_after: u64,
        receipt: &TurnReceipt,
    ) -> Result<(), String>;
    /// Load the durable log back as an [`OrchestrationLog`] (the receipt chain + per-step records).
    fn load(&self) -> Result<OrchestrationLog, String>;
}

/// The in-memory durable log — the in-process stand-in for the `dregg.commit_log` table. Keeps the
/// committed [`crate::LoggedStep`]s; survives an engine drop (the "crash"), so [`crate::recover`]
/// rebuilds from it alone. Mirrors pg-dregg's `MemLog`.
#[derive(Clone, Debug, Default)]
pub struct MemLog {
    log: OrchestrationLog,
}

impl MemLog {
    /// A fresh, empty durable sink.
    pub fn new() -> Self {
        Self::default()
    }
    /// How many steps are durably committed.
    pub fn len(&self) -> usize {
        self.log.len()
    }
    /// Whether nothing is committed yet.
    pub fn is_empty(&self) -> bool {
        self.log.is_empty()
    }
    /// The underlying [`OrchestrationLog`] (the receipt chain the auditor verifies).
    pub fn orchestration_log(&self) -> &OrchestrationLog {
        &self.log
    }
}

impl DurableLog for MemLog {
    fn append(
        &mut self,
        step: &WorkStep,
        spent_after: u64,
        receipt: &TurnReceipt,
    ) -> Result<(), String> {
        self.log.entries.push(crate::LoggedStep {
            step: step.clone(),
            spent_after,
            receipt: receipt.clone(),
        });
        Ok(())
    }
    fn load(&self) -> Result<OrchestrationLog, String> {
        Ok(self.log.clone())
    }
}

/// The outcome of a durable run/resume — the counts that prove exactly-once.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DurableOutcome {
    /// Steps newly committed (each a verified turn checkpointed to the durable log).
    pub committed: usize,
    /// Steps SKIPPED because they were already durable (never re-applied — the exactly-once tooth).
    pub skipped: usize,
}

/// A **durable orchestration** — the verified-turn step driver wrapped in the pg-dregg durable-workflow
/// shape. It owns an [`OrchestrationEngine`] and drives each [`WorkStep`] as a verified turn,
/// checkpointing the committed receipt to a [`DurableLog`] the instant it commits. After a crash (the
/// engine dropped, the durable log surviving), [`DurableOrchestration::recover`] rebuilds the resumable
/// state and [`DurableOrchestration::resume`] finishes the uncommitted tail exactly-once.
pub struct DurableOrchestration<'a> {
    engine: OrchestrationEngine<'a>,
}

impl<'a> DurableOrchestration<'a> {
    /// Wrap an [`OrchestrationEngine`] in the durable-workflow driver.
    pub fn new(engine: OrchestrationEngine<'a>) -> Self {
        Self { engine }
    }

    /// Borrow the inner engine (e.g. to read running spend or the open receipt for the audit).
    pub fn engine(&self) -> &OrchestrationEngine<'a> {
        &self.engine
    }

    /// The open-board receipt (the chain predecessor for the first step) — needed by [`crate::recover`]
    /// / [`crate::audit_run`]. `None` until the board is opened (by [`DurableOrchestration::run`]).
    pub fn open_receipt(&self) -> Option<&TurnReceipt> {
        self.engine.open_receipt()
    }

    /// **RUN DURABLE** — open the board, then drive each [`WorkStep`] as a verified turn, appending the
    /// committed receipt to `durable` the instant it commits (the checkpoint). Returns the
    /// [`DurableOutcome`]. A refused step (out-of-mandate or executor-refused) STOPS the run and is
    /// returned; the durable log holds exactly the committed prefix (the crash-consistent shape). The
    /// in-process face of pg-dregg's `run_durable`.
    pub fn run<L: DurableLog>(
        &mut self,
        lead: &str,
        plan: &[WorkStep],
        durable: &mut L,
    ) -> Result<DurableOutcome, OrchestrationError> {
        self.engine.open(lead)?;
        // The engine's own log mirrors the durable sink; we keep them in lockstep so a recover can read
        // either. (In pg-dregg the materialized mirror + the commit_log are the two faces; here the
        // engine's `OrchestrationLog` is the mirror and `durable` is the commit_log.)
        let mut mirror = OrchestrationLog::new();
        let mut committed = 0usize;
        for step in plan {
            let receipt = self.engine.step(step, &mut mirror)?;
            let spent_after = self.engine.spent(step.worker);
            durable
                .append(step, spent_after, &receipt)
                .map_err(OrchestrationError::Refused)?;
            committed += 1;
        }
        Ok(DurableOutcome {
            committed,
            skipped: 0,
        })
    }

    /// **RECOVER** — re-validate the durable log after a crash and re-derive the resumable state (the
    /// per-worker spend + next epoch), rebuilding from the log ALONE. A log that does not chain is a
    /// corrupted store and is surfaced ([`AuditError`]), never silently resumed. Returns the
    /// [`RecoveredState`] to pass to [`DurableOrchestration::resume_state`]. The in-process face of
    /// pg-dregg's `recover_from_durable`.
    pub fn recover<L: DurableLog>(
        open_receipt: &TurnReceipt,
        durable: &L,
    ) -> Result<(OrchestrationLog, RecoveredState), AuditError> {
        let log = durable
            .load()
            .map_err(|e| AuditError::OverMandate { ordinal: 0, why: e })?;
        let state = recover(open_receipt, &log)?;
        Ok((log, state))
    }

    /// Re-seat the inner engine's resumable state after a recover (the per-worker spend + next epoch +
    /// open receipt), so [`DurableOrchestration::resume`] can finish the tail exactly-once.
    pub fn resume_state(&mut self, recovered: RecoveredState, open_receipt: TurnReceipt) {
        self.engine.resume_state(recovered, open_receipt);
    }

    /// **RESUME DURABLE** — finish a `plan` whose committed prefix is already in `durable`. The committed
    /// steps are SKIPPED (the index-skip fast path + the no-replay-epoch backstop), never re-applied;
    /// only the uncommitted TAIL is submitted, each checkpointed to `durable`. Returns the
    /// [`DurableOutcome`] (`skipped` = the prefix, `committed` = the tail). The in-process face of
    /// pg-dregg's `resume_durable`. Requires [`DurableOrchestration::resume_state`] first.
    pub fn resume<L: DurableLog>(
        &mut self,
        plan: &[WorkStep],
        durable: &mut L,
    ) -> Result<DurableOutcome, OrchestrationError> {
        let done = durable.load().map(|l| l.len()).unwrap_or(0).min(plan.len());
        let tail = &plan[done..];
        let mut mirror = OrchestrationLog::new();
        let mut committed = 0usize;
        for step in tail {
            let receipt = self.engine.step(step, &mut mirror)?;
            let spent_after = self.engine.spent(step.worker);
            durable
                .append(step, spent_after, &receipt)
                .map_err(OrchestrationError::Refused)?;
            committed += 1;
        }
        Ok(DurableOutcome {
            committed,
            skipped: done,
        })
    }
}

/// Build a [`DurableOrchestration`] from the orchestration pieces — convenience constructor mirroring
/// pg-dregg's `WorkflowEngine::new`. The coordinator's held mandate + the two workers' attenuated
/// mandates (each must be `⊑` the coordinator's; see [`Mandate::le`]).
pub fn durable_orchestration<'a>(
    cipherclerk: &'a dregg_app_framework::AppCipherclerk,
    exec: &'a dregg_app_framework::EmbeddedExecutor,
    board: dregg_app_framework::CellId,
    coordinator: Mandate,
    worker_a_mandate: Mandate,
    worker_b_mandate: Mandate,
) -> DurableOrchestration<'a> {
    DurableOrchestration::new(OrchestrationEngine::new(
        cipherclerk,
        exec,
        board,
        coordinator,
        worker_a_mandate,
        worker_b_mandate,
    ))
}

/// The result of a cold rebuild: the freshly-re-executed durable log + the proof the rebuild matches.
#[derive(Clone, Debug)]
pub struct ColdRebuild {
    /// The receipt log re-executed from the durable plan into a FRESH ledger (every step a verified
    /// turn, re-run from genesis). Its receipt chain is independently auditable ([`crate::audit_run`]).
    pub rebuilt: OrchestrationLog,
    /// Whether the rebuilt run reached the SAME per-worker spend totals as the original durable run
    /// (the materialized state is reconstructed from the log alone — a self-checking store).
    pub spend_matches: bool,
}

/// **COLD REBUILD — re-execute the whole durable run from the log alone into a FRESH ledger.**
///
/// [`crate::recover`] re-validates the receipt chain and re-derives the spend meters assuming the
/// materialized ledger survived (the warm path — pg-dregg's mirror + commit_log both persist). This is
/// the COLD path: nothing of the live state survives EXCEPT the durable log's `WorkStep`s, and the
/// verified state is RECONSTRUCTED by re-running every step as a verified turn from genesis. The fresh
/// `cclerk`/`exec` own a brand-new ledger; `born_board` is a freshly-born coordinator cell on it (the
/// caller births it the same way the original did). Each logged step is re-submitted through the
/// verified executor — so the rebuild is not a copy of bytes but a RE-DERIVATION of the state through
/// the same gates (an attacker who tampered the durable plan could not make a bad step re-execute: the
/// executor's mandate/budget/no-replay gates refuse it on the way up). The in-process face of pg-dregg's
/// `recover_from_durable` re-execution.
///
/// Returns the rebuilt log + whether its spend totals match the original (`durable`). The rebuilt chain
/// is independently auditable; a tampered durable plan that would re-execute a bad step fails here
/// (the step is refused), surfacing as `Err`.
pub fn cold_rebuild<L: DurableLog>(
    cclerk: &dregg_app_framework::AppCipherclerk,
    exec: &dregg_app_framework::EmbeddedExecutor,
    born_board: dregg_app_framework::CellId,
    coordinator: Mandate,
    worker_a_mandate: Mandate,
    worker_b_mandate: Mandate,
    lead: &str,
    durable: &L,
) -> Result<ColdRebuild, OrchestrationError> {
    let original = durable.load().map_err(OrchestrationError::Refused)?;
    // The plan, recovered from the durable log: the SAME sequence of WorkSteps, in commit order.
    let plan: Vec<WorkStep> = original.entries.iter().map(|e| e.step.clone()).collect();

    // A fresh engine on the fresh ledger — re-run open + every step as a verified turn from genesis.
    let mut engine = OrchestrationEngine::new(
        cclerk,
        exec,
        born_board,
        coordinator,
        worker_a_mandate,
        worker_b_mandate,
    );
    let mut rebuilt = OrchestrationLog::new();
    engine.open(lead)?;
    for step in &plan {
        // Re-execute the step through the verified executor — its mandate/budget/no-replay gates
        // re-decide it. A tampered durable plan that would re-run a bad step is REFUSED here.
        engine.step(step, &mut rebuilt)?;
    }

    // Self-check: the rebuilt run reached the same per-worker spend as the original.
    let orig_spend = derive_spend(&original);
    let rebuilt_spend = derive_spend(&rebuilt);
    Ok(ColdRebuild {
        rebuilt,
        spend_matches: orig_spend == rebuilt_spend,
    })
}

/// The per-worker spend totals (A, B) re-derived from a log's post-images.
fn derive_spend(log: &OrchestrationLog) -> (u64, u64) {
    let mut a = 0u64;
    let mut b = 0u64;
    for e in &log.entries {
        match e.step.worker {
            WorkerSlot::A => a = e.spent_after,
            WorkerSlot::B => b = e.spent_after,
        }
    }
    (a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Tool, coordinator_child_program_vk, orchestration_factory_descriptor};
    use dregg_app_framework::{
        AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, EmbeddedExecutor,
    };
    use dregg_cell::FactoryCreationParams;

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
        let birth =
            cclerk.create_from_factory(crate::ORCHESTRATION_FACTORY_VK, owner, token, params);
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
        let c = Mandate::coordinator(
            [Tool::Read, Tool::Search, Tool::Summarize, Tool::Write],
            1000,
            "task",
        );
        let a = c.attenuate([Tool::Read, Tool::Search, Tool::Summarize], 700, "research");
        let b = c.attenuate([Tool::Read], 300, "fact-check");
        (c, a, b)
    }

    #[test]
    fn durable_run_checkpoints_each_verified_turn() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x71u8; 32]);
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        let board = born_board(&cclerk, &exec, b"durable-run");
        let (c, a, b) = mandates();

        let plan = vec![
            WorkStep::new(WorkerSlot::A, Tool::Search, 250, "s"),
            WorkStep::new(WorkerSlot::B, Tool::Read, 150, "r"),
        ];
        let mut durable = MemLog::new();
        let mut d = durable_orchestration(&cclerk, &exec, board, c, a, b);
        let out = d
            .run("lead", &plan, &mut durable)
            .expect("durable run commits");
        assert_eq!(out.committed, 2);
        assert_eq!(out.skipped, 0);
        assert_eq!(
            durable.len(),
            2,
            "each verified turn checkpointed to the durable log"
        );
    }

    #[test]
    fn durable_crash_recover_resume_is_exactly_once() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x72u8; 32]);
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        let board = born_board(&cclerk, &exec, b"durable-eo");
        let (c, a, b) = mandates();

        let plan = vec![
            WorkStep::new(WorkerSlot::A, Tool::Search, 250, "s1"),
            WorkStep::new(WorkerSlot::A, Tool::Summarize, 200, "s2"),
            WorkStep::new(WorkerSlot::B, Tool::Read, 150, "r1"),
            WorkStep::new(WorkerSlot::B, Tool::Read, 100, "r2"),
        ];
        let mut durable = MemLog::new();
        let open_receipt;

        // Run the prefix, then "crash" (drop the durable orchestration).
        {
            let mut d =
                durable_orchestration(&cclerk, &exec, board, c.clone(), a.clone(), b.clone());
            d.run("lead", &plan[..2], &mut durable)
                .expect("prefix commits");
            open_receipt = d.open_receipt().cloned().expect("open receipt");
            assert_eq!(durable.len(), 2);
        }

        // Recover from the durable log alone.
        let (_log, recovered) =
            DurableOrchestration::recover(&open_receipt, &durable).expect("recover re-validates");
        assert_eq!(recovered.spent_a, 450);
        assert_eq!(recovered.spent_b, 0);

        // Resume the SAME plan — the prefix is skipped, only the tail runs.
        {
            let mut d =
                durable_orchestration(&cclerk, &exec, board, c.clone(), a.clone(), b.clone());
            d.resume_state(recovered, open_receipt.clone());
            let out = d.resume(&plan, &mut durable).expect("the tail finishes");
            assert_eq!(
                out.skipped, 2,
                "the committed prefix is skipped, never re-applied"
            );
            assert_eq!(out.committed, 2, "only the tail runs");
        }
        assert_eq!(
            durable.len(),
            4,
            "four turns total — exactly-once, no double-apply"
        );

        // The whole durable run audits clean.
        let log = durable.orchestration_log();
        let ok = crate::audit_run(&open_receipt, log, &c, &a, &b).expect("audits");
        assert_eq!(ok.steps, 4);
        assert_eq!(ok.spent_a, 450);
        assert_eq!(ok.spent_b, 250);
    }

    #[test]
    fn cold_rebuild_reconstructs_the_state_from_the_log_alone() {
        // Run a durable orchestration on ledger #1, then COLD-rebuild it into a brand-new ledger #2
        // (a fresh executor with nothing but the durable log's WorkSteps) — re-executing every step
        // as a verified turn from genesis. The reconstructed state must match.
        let (c, a, b) = mandates();
        let plan = vec![
            WorkStep::new(WorkerSlot::A, Tool::Search, 250, "s1"),
            WorkStep::new(WorkerSlot::A, Tool::Summarize, 200, "s2"),
            WorkStep::new(WorkerSlot::B, Tool::Read, 150, "r1"),
        ];

        // --- Original run on ledger #1 ---
        let mut durable = MemLog::new();
        {
            let cclerk1 = AppCipherclerk::new(AgentCipherclerk::new(), [0x73u8; 32]);
            let exec1 = EmbeddedExecutor::new(&cclerk1, "default");
            let board1 = born_board(&cclerk1, &exec1, b"cold-orig");
            let mut d =
                durable_orchestration(&cclerk1, &exec1, board1, c.clone(), a.clone(), b.clone());
            d.run("lead", &plan, &mut durable)
                .expect("original run commits");
            assert_eq!(durable.len(), 3);
        }
        // ledger #1 is GONE — only `durable` (the log) survives.

        // --- COLD rebuild into ledger #2 (fresh executor, fresh board) ---
        let cclerk2 = AppCipherclerk::new(AgentCipherclerk::new(), [0x74u8; 32]);
        let exec2 = EmbeddedExecutor::new(&cclerk2, "default");
        let board2 = born_board(&cclerk2, &exec2, b"cold-rebuild");
        let rebuild = cold_rebuild(
            &cclerk2,
            &exec2,
            board2,
            c.clone(),
            a.clone(),
            b.clone(),
            "lead",
            &durable,
        )
        .expect("the cold rebuild re-executes every step from genesis");
        // The reconstructed state matches the original (the log alone reconstructs the verified state).
        assert!(
            rebuild.spend_matches,
            "cold-rebuilt spend matches the original durable run"
        );
        assert_eq!(rebuild.rebuilt.len(), 3);
        // The rebuilt run is independently auditable.
        let open2 = exec2; // (keep exec2 alive; board2 state lives in its ledger)
        let _ = open2;
        let (ra, rb) = {
            let mut a_spent = 0u64;
            let mut b_spent = 0u64;
            for e in &rebuild.rebuilt.entries {
                match e.step.worker {
                    WorkerSlot::A => a_spent = e.spent_after,
                    WorkerSlot::B => b_spent = e.spent_after,
                }
            }
            (a_spent, b_spent)
        };
        assert_eq!(ra, 450, "worker-A reconstructed to 450");
        assert_eq!(rb, 150, "worker-B reconstructed to 150");
    }

    #[test]
    fn cold_rebuild_of_a_tampered_plan_refuses_the_bad_step() {
        // A durable plan tampered to insert an OVER-BUDGET step fails the cold rebuild: the bad step
        // is REFUSED by the executor's AffineLe gate on re-execution (the rebuild is a re-derivation
        // through the gates, not a byte copy).
        let (c, a, b) = mandates();
        // Build a durable log whose recorded plan includes a step that, re-executed, breaches budget:
        // worker-A spends 700 (its whole sub-budget) then a SECOND 700 (over the 1000 swarm budget).
        let plan = [
            WorkStep::new(WorkerSlot::A, Tool::Search, 700, "s1"),
            WorkStep::new(WorkerSlot::B, Tool::Read, 700, "s2-too-much"),
        ];
        // We can't even RUN this honestly (the second breaches on ledger #1 too), so we hand-craft a
        // durable log carrying both step records as if a tamperer wrote them, then rebuild.
        let cclerk1 = AppCipherclerk::new(AgentCipherclerk::new(), [0x75u8; 32]);
        let exec1 = EmbeddedExecutor::new(&cclerk1, "default");
        let board1 = born_board(&cclerk1, &exec1, b"cold-tamper-src");
        let mut durable = MemLog::new();
        {
            // Commit only the first (legal) step honestly so the log has a real receipt to chain.
            let mut d =
                durable_orchestration(&cclerk1, &exec1, board1, c.clone(), a.clone(), b.clone());
            d.run("lead", &plan[..1], &mut durable)
                .expect("first step commits");
        }
        // Tamper: append the over-budget step record (with the first step's receipt as a stand-in).
        let stolen = durable.orchestration_log().entries[0].receipt.clone();
        durable
            .append(&plan[1], 700, &stolen)
            .expect("append the tampered record");

        // COLD rebuild MUST refuse: re-executing the over-budget step is rejected by the AffineLe gate.
        let cclerk2 = AppCipherclerk::new(AgentCipherclerk::new(), [0x76u8; 32]);
        let exec2 = EmbeddedExecutor::new(&cclerk2, "default");
        let board2 = born_board(&cclerk2, &exec2, b"cold-tamper-dst");
        let err = cold_rebuild(&cclerk2, &exec2, board2, c, a, b, "lead", &durable)
            .expect_err("a tampered over-budget plan must fail the cold rebuild");
        assert!(
            matches!(
                err,
                OrchestrationError::Refused(_) | OrchestrationError::OutOfMandate { .. }
            ),
            "the bad step is refused on re-execution, got {err:?}"
        );
    }
}
