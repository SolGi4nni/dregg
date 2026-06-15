//! # starbridge-agent-orchestration
//!
//! **Verifiable DURABLE + AUDITABLE multi-agent orchestration** — agents are intricate LOOPS that
//! live ABOVE dregg; dregg owns the ONE seam that matters (the tool-call / verified-turn boundary) and
//! this app makes that seam legible AND durable AND auditable for a whole orchestration:
//!
//!   * a **COORDINATOR** cell holds the task and issues each **WORKER** an **ATTENUATED MANDATE** — a
//!     capability strictly weaker than the coordinator's own ([`Mandate`]: a scope-narrowed
//!     **tool-set** ∧ a **sub-budget** ∧ a **sub-task**; `granted ⊑ held`, the proven
//!     non-amplification, [`Mandate::le`] / [`Mandate::attenuate`]);
//!   * **every worker action is a cap-gated VERIFIED TURN** through the real embedded executor — a
//!     worker that reaches for a WIDER tool, an OVER-budget spend, or an OUT-OF-scope cell is REFUSED,
//!     fail-closed, IN THE FIRE PATH (the executor's `AffineLe` budget tooth + the capability gate +
//!     the off-ledger mandate pre-check that provably agrees);
//!   * the whole orchestration is a **DURABLE workflow** — each step a verified turn checkpointed to a
//!     receipt log ([`OrchestrationLog`]); crash-recoverable; **exactly-once** on resume (modeled on
//!     `pg-dregg::workflow`'s `run_durable` / `recover_from_durable` / `resume_durable`);
//!   * it is **AUDITABLE** — an auditor (a light client) re-derives the run from the receipt chain and
//!     verifies **no agent ever exceeded its mandate** ([`audit_run`]: pairwise `dregg_turn::verify_receipt_extends`
//!     over the chained [`dregg_turn::TurnReceipt`]s + the per-step mandate re-check). A clean run audits
//!     OK; a **tampered** receipt (broken hash/state chain) or an **over-mandate** step is DETECTABLE.
//!
//! ## What this is, and how it differs from `swarm-orchestration`
//!
//! The sibling crate `starbridge-swarm-orchestration` proves the *in-memory* shape: a coordinator
//! dispatch-board cell, cap-attenuated dispatch, the budget tooth, the over-grant refusal. THIS crate
//! is the **durable + auditable** shape: the SAME real primitives (an [`dregg_app_framework::EmbeddedExecutor`]
//! verified turn, a factory-born coordinator cell whose installed [`dregg_app_framework::CellProgram`] IS
//! the budget policy, a cap-attenuated worker mandate) wrapped in a durable workflow engine
//! ([`OrchestrationEngine`]) whose receipt log survives a crash and whose receipt chain is the audit
//! trail. The mandate is upgraded to a first-class attenuation *triple* (`tools ∧ budget ∧ sub_task`)
//! with an explicit `granted ⊑ held` lattice — the Rust image of the Lean
//! `worker_authority_subset_orchestrator` keystone.
//!
//! ## The verified Lean developments this is the executable surface of
//!
//! | Lean keystone                                            | What it guarantees / what this crate enforces |
//! |---------------------------------------------------------|-----------------------------------------------|
//! | `AgentOrchestration.worker_authority_subset_orchestrator` | **non-amplification**: a worker's reach ⊆ the coordinator's ([`Mandate::le`]) |
//! | `AgentOrchestration.worker_attenuation_is_strict`         | the subset is STRICT: the coordinator holds a tool/right the worker mandate drops |
//! | `AgentOrchestration.workForest_conserves`                 | the orchestration's value moves CONSERVE (no mint/burn) |
//! | `AgentOrchestration.badWorkerForest_fails_closed`         | a worker's out-of-mandate action returns `none` — the whole forest rejects |
//! | `AgentOrchestrationBudget.affineLe [(1,spentA),(1,spentB)] mandate` | **atomic budget**: `Σ worker spend <= mandate` — an over-budget dispatch is REFUSED |
//! | `AgentOrchestrationBudget.immutable budgetF` / `strictMono epochF`  | the mandate is frozen; every step strictly advances the epoch (no replay) |
//! | `Deos.WorkflowBridge.workflowStep_is_gatedAffordance`     | a workflow step IS a cap∧state affordance fire — the durable surface RENDERS the choreography |
//! | `Protocol.Workflow.exec_authorized` / `exec_in_order`     | a step commits ONLY when authorized + in the precondition phase — the choreography order |
//!
//! ## The narration-vs-truth property
//!
//! What the orchestration DID is provable, not what it claims. A worker loop could lie about "I was
//! authorized", "I stayed within my mandate", "I called only the tools I was granted" — but the
//! cap-gate REFUSAL, the executor's receipt chain, and the audit's per-step mandate re-check are the
//! on-ledger truth. An auditor reviews an orchestration she did not write and could not trust, and is
//! nonetheless never fooled.

#![forbid(unsafe_code)]

/// The orchestration board re-expressed as a composed [`dregg_app_framework::DeosApp`] — the live,
/// per-viewer, cap-gated web surface (the auditor ⊂ worker ⊂ coordinator rights ladder, the gated
/// `worker_step` htmx tooth, the mounted axum surface, the web-of-cells publish).
pub mod deos;

/// The orchestration re-expressed as a pg-dregg-shaped DURABLE WORKFLOW — DBOS-style durable execution
/// where every step is a verified turn (checkpoint each committed receipt; crash-recoverable;
/// exactly-once on resume; COLD-REBUILD by re-execution from the log alone). Models `pg-dregg::workflow`
/// without depending on it (it is a standalone workspace); names the bridge explicitly.
pub mod durable;

/// Live MCP tool-call binding — an agent loop's `tools/call` invocation run AS a verified worker step,
/// so the receipt cryptographically binds the exact tool + arguments and a call outside the worker's
/// mandate is refused in the fire path.
pub mod mcp;

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, ConstantsModule, Effect, EmbeddedExecutor, Event, FactoryDescriptor,
    FieldElement, InspectorDescriptor, StarbridgeAppContext, StateConstraint, canonical_program_vk,
    field_from_u64, hex_encode_32, symbol,
};
use dregg_turn::{TurnReceipt, VerifyError, verify_receipt_extends};
use std::collections::BTreeSet;

pub use dregg_app_framework::field_from_bytes;

/// Verify that `receipts` form one contiguous, intact chain — each receipt correctly EXTENDS its
/// predecessor (agent consistency + hash-chain continuity + state continuity). Unlike
/// `dregg_turn::verify_receipt_chain` (which requires the FIRST receipt to be the agent's genesis,
/// `previous_receipt_hash == None`), this checks a contiguous WINDOW of an agent's chain pairwise via
/// `dregg_turn::verify_receipt_extends` — which is exactly right here: the orchestration's receipts are
/// the window AFTER the coordinator's birth receipt, so `open` is not genesis. A tampered, reordered,
/// or substituted receipt anywhere in the window breaks the link and is surfaced as [`VerifyError`].
fn verify_receipt_window(receipts: &[TurnReceipt]) -> Result<(), VerifyError> {
    for pair in receipts.windows(2) {
        verify_receipt_extends(&pair[0], &pair[1])?;
    }
    Ok(())
}

// =============================================================================
// §1 — The MANDATE: an attenuation triple (tool-set ∧ sub-budget ∧ sub-task),
// with the `granted ⊑ held` lattice — the Rust image of the Lean orchestrator →
// worker `keep`-attenuation (`AgentOrchestration.workerKeep ⊑ orchestratorCap`).
// =============================================================================

/// A **tool** the orchestration's agents may invoke (the scope dimension of a [`Mandate`]). A
/// coordinator holds a broad tool-set; a worker is handed a NARROWED subset. Modeled on the Lean
/// authority rights (`[read, write]` etc.) — the worker `keep` drops at least one.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum Tool {
    /// Read a document / fetch a URL (the least-privilege baseline).
    Read,
    /// Search an index / corpus.
    Search,
    /// Summarize / transform fetched content.
    Summarize,
    /// Write back into the shared workspace (a privileged tool — the strict-attenuation witness).
    Write,
    /// Spend from the treasury / pay an external API (the most privileged tool).
    Spend,
}

impl Tool {
    /// A short legible label for receipts / activity feeds / event topics.
    pub fn label(self) -> &'static str {
        match self {
            Tool::Read => "read",
            Tool::Search => "search",
            Tool::Summarize => "summarize",
            Tool::Write => "write",
            Tool::Spend => "spend",
        }
    }
}

/// A **mandate** the coordinator confers on a worker: the worker may invoke ONLY the [`Mandate::tools`]
/// it lists, may spend AT MOST [`Mandate::budget`], and is scoped to the sub-task [`Mandate::sub_task`].
/// A mandate is an element of a lattice ordered by attenuation: `granted ⊑ held` ([`Mandate::le`]) iff
/// the granted tool-set is a SUBSET and the granted budget is NO LARGER. [`Mandate::attenuate`] produces
/// a mandate `⊑` the original — never wider. This is the `derive_no_amplify` shadow: you can only narrow.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Mandate {
    /// The tools the holder may invoke (the SCOPE). A worker's set is a subset of the coordinator's.
    pub tools: BTreeSet<Tool>,
    /// The spend ceiling (the conserved BUDGET column the executor's `AffineLe` gate sums). A worker's
    /// budget is no larger than the share the coordinator allots from the swarm mandate.
    pub budget: u64,
    /// The sub-task the mandate is scoped to (the labeled work item — also the audit topic).
    pub sub_task: String,
}

impl Mandate {
    /// The coordinator's own (broad) mandate over a task: all the tools it is willing to delegate, the
    /// full swarm budget, and the top-level task label.
    pub fn coordinator(tools: impl IntoIterator<Item = Tool>, budget: u64, task: &str) -> Self {
        Self {
            tools: tools.into_iter().collect(),
            budget,
            sub_task: task.to_string(),
        }
    }

    /// **`granted ⊑ held`** — does `self` (the granted/worker mandate) sit BELOW `held` (the
    /// coordinator's) in the attenuation lattice? True iff `self.tools ⊆ held.tools` AND
    /// `self.budget <= held.budget`. (The sub-task is a label, not part of the order — a coordinator
    /// scopes a worker to any sub-task it likes; what cannot be amplified is the tool-set and the
    /// budget.) The Rust image of `AgentOrchestration.worker_authority_subset_orchestrator`.
    pub fn le(&self, held: &Mandate) -> bool {
        self.tools.is_subset(&held.tools) && self.budget <= held.budget
    }

    /// **`attenuate`** — derive a worker mandate from `self` by INTERSECTING the requested tools with
    /// what is held, CLAMPING the requested budget to what is held, and labeling the sub-task. The
    /// result is GUARANTEED `⊑ self` (`derive_no_amplify`: the output is always a narrowing). A request
    /// for a tool the coordinator does not hold is simply absent from the result; a request for more
    /// budget than held is clamped down — you can never amplify past what you hold.
    pub fn attenuate(
        &self,
        request_tools: impl IntoIterator<Item = Tool>,
        request_budget: u64,
        sub_task: &str,
    ) -> Mandate {
        let requested: BTreeSet<Tool> = request_tools.into_iter().collect();
        Mandate {
            tools: requested.intersection(&self.tools).copied().collect(),
            budget: request_budget.min(self.budget),
            sub_task: sub_task.to_string(),
        }
    }

    /// Whether this mandate AUTHORIZES a single worker action: invoking `tool` at `cost`, given the
    /// worker's `prior_spent` under this mandate. Fail-closed on each axis:
    ///   * SCOPE:  `tool ∈ self.tools` (the granted tool-set);
    ///   * BUDGET: `prior_spent + cost <= self.budget` (the conserved ceiling).
    ///
    /// This is the OFF-LEDGER mandate pre-check — the coordinator/worker checks it BEFORE building the
    /// turn (fail-closed: it does not even submit an out-of-mandate action), AND the executor
    /// independently re-checks the budget on commit (the real `AffineLe` gate). Two gates that
    /// provably agree. The audit ([`audit_run`]) re-runs this check per step over the receipt chain.
    pub fn authorizes(&self, tool: Tool, prior_spent: u64, cost: u64) -> bool {
        self.tools.contains(&tool) && prior_spent.saturating_add(cost) <= self.budget
    }
}

// =============================================================================
// §2 — The coordinator dispatch-board cell (the budget policy as a CellProgram).
// The board carries the conserved spend meters + the no-replay epoch; the
// per-worker mandate's BUDGET share is metered here and the executor's `AffineLe`
// gate enforces `Σ worker spend <= mandate` on EVERY touching turn.
// =============================================================================

/// Slot 0 — `LEAD`. The appointed coordinator's identity scalar (the signed-provenance anchor).
/// `WriteOnce`. The Lean `leadF`.
pub const LEAD_SLOT: u8 = 0;
/// Slot 1 — `BUDGET`. The swarm spend mandate (the conserved ceiling, `Σ worker budgets <= this`).
/// `WriteOnce` — never widened mid-run. The Lean `budgetF` (`immutable budgetF`).
pub const BUDGET_SLOT: u8 = 1;
/// Slot 2 — `SPENT_A`. Worker-A's cumulative spend. `Monotonic` — never rolled back. The Lean `spentAF`.
pub const SPENT_A_SLOT: u8 = 2;
/// Slot 3 — `SPENT_B`. Worker-B's cumulative spend. `Monotonic`. The Lean `spentBF`.
pub const SPENT_B_SLOT: u8 = 3;
/// Slot 4 — `EPOCH`. The strictly-monotone dispatch counter (no replay). `StrictMonotonic`. The Lean
/// `epochF` (`strictMono epochF`).
pub const EPOCH_SLOT: u8 = 4;

/// The coordinator dispatch-board POLICY as a flat conjunction of slot caveats — the Rust transcription
/// of the Lean `AgentOrchestrationBudget.dispatchConstraints`. THIS is the predicate the executor
/// installs as the factory-born coordinator's `CellProgram` and re-checks on EVERY touching turn:
///
///   * **atomic budget** (`AffineLe`): `spent_a + spent_b - budget <= 0` — the agents COLLECTIVELY never
///     spend more than the swarm mandate. An over-budget dispatch is REFUSED; the whole turn aborts
///     (it is ONE predicate). The Lean `affineLe [(1,spentAF),(1,spentBF)] mandate`.
///   * **write-once mandate / lead** (`WriteOnce BUDGET/LEAD`): bound once at board open (from zero),
///     frozen thereafter — born-empty-compatible (`Immutable` would freeze AT ZERO and refuse the open
///     turn; mirror swarm-orchestration / tool-access-delegation / bounty-board).
///   * **monotone meters** (`Monotonic SPENT_A/SPENT_B`): a worker's spend only accumulates.
///   * **no replay** (`StrictMonotonic EPOCH`): every touching turn strictly advances the epoch.
pub fn coordinator_constraints() -> Vec<StateConstraint> {
    vec![
        StateConstraint::AffineLe {
            terms: vec![(1, SPENT_A_SLOT), (1, SPENT_B_SLOT), (-1, BUDGET_SLOT)],
            c: 0,
        },
        StateConstraint::WriteOnce { index: BUDGET_SLOT },
        StateConstraint::WriteOnce { index: LEAD_SLOT },
        StateConstraint::Monotonic {
            index: SPENT_A_SLOT,
        },
        StateConstraint::Monotonic {
            index: SPENT_B_SLOT,
        },
        StateConstraint::StrictMonotonic { index: EPOCH_SLOT },
    ]
}

/// The COORDINATOR dispatch-board program — `coordinator_constraints` as a `CellProgram::Predicate`,
/// identical to what the factory installs on the born cell.
pub fn coordinator_program() -> CellProgram {
    CellProgram::Predicate(coordinator_constraints())
}

/// Canonical child program VK for the coordinator dispatch-board cell.
pub fn coordinator_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&coordinator_program())
}

/// The factory VK we publish for the agent-orchestration coordinator factory.
pub const ORCHESTRATION_FACTORY_VK: [u8; 32] = *b"starbridge-agent-orchestr-factry";

/// Default per-epoch creation budget for the coordinator factory.
pub const DEFAULT_CREATION_BUDGET: u64 = 256;

/// Hash an agent identity string to its field scalar (the board stores `LEAD` as this scalar).
pub fn identity_field(agent: &str) -> FieldElement {
    field_from_bytes(agent.as_bytes())
}

/// Build the [`FactoryDescriptor`] for agent-orchestration coordinator (dispatch-board) cells. A
/// factory-born coordinator is born EMPTY; the `open_board` turn binds `LEAD` + `BUDGET` (from zero,
/// under `WriteOnce`) before any dispatch, and the budget gate + meters + epoch caveats are installed
/// at birth FOR LIFE.
pub fn orchestration_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: ORCHESTRATION_FACTORY_VK,
        child_program_vk: Some(coordinator_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(coordinator_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            // The coordinator holds an attenuatable SelfCell cap — the ocap handle it dispatches under.
            // Sub-delegation to workers NARROWS it ([`Mandate::attenuate`] — no amplification).
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: coordinator_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![orchestration_factory_descriptor()]
}

/// Which of the two worker spend-meters a worker draws against. The two-meter budget is what no single
/// counter sees: the affine-sum bound `spent_a + spent_b <= budget`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum WorkerSlot {
    /// Worker-A — cumulative spend in `SPENT_A`.
    A,
    /// Worker-B — cumulative spend in `SPENT_B`.
    B,
}

impl WorkerSlot {
    /// The board slot this worker's cumulative spend accumulates in.
    pub fn spend_slot(self) -> u8 {
        match self {
            WorkerSlot::A => SPENT_A_SLOT,
            WorkerSlot::B => SPENT_B_SLOT,
        }
    }
    /// A short legible label.
    pub fn label(self) -> &'static str {
        match self {
            WorkerSlot::A => "worker-a",
            WorkerSlot::B => "worker-b",
        }
    }
}

// =============================================================================
// §3 — Turn builders (OPEN BOARD / WORKER STEP). Each is a real signed Action;
// a worker step advances the worker's meter (summed by the AffineLe gate) +
// the no-replay epoch + emits a content-addressed action record (the receipt's
// audit payload binds the tool, cost, and sub-task the worker claimed to act on).
// =============================================================================

/// **OPEN BOARD** — the coordinator opens the dispatch board by pinning the `LEAD` identity and the
/// `BUDGET` mandate (`WriteOnce`: bound once from zero, frozen), the two meters born at 0, and the
/// epoch advanced to 1 (so the open turn itself satisfies `StrictMonotonic(EPOCH)`, 0 -> 1).
pub fn build_open_board_action(
    cipherclerk: &AppCipherclerk,
    board: CellId,
    lead: &str,
    budget: u64,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: board,
            index: LEAD_SLOT as usize,
            value: identity_field(lead),
        },
        Effect::SetField {
            cell: board,
            index: BUDGET_SLOT as usize,
            value: field_from_u64(budget),
        },
        Effect::SetField {
            cell: board,
            index: SPENT_A_SLOT as usize,
            value: field_from_u64(0),
        },
        Effect::SetField {
            cell: board,
            index: SPENT_B_SLOT as usize,
            value: field_from_u64(0),
        },
        Effect::SetField {
            cell: board,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(1),
        },
        Effect::EmitEvent {
            cell: board,
            event: Event::new(
                symbol("orchestration-board-opened"),
                vec![identity_field(lead), field_from_u64(budget)],
            ),
        },
    ];
    cipherclerk.make_action(board, "open_board", effects)
}

/// **WORKER STEP** — a worker performs one mandated action: it advances ITS cumulative spend meter on
/// the board by `cost` (`Monotonic`; summed by the `AffineLe` budget gate), advances the epoch
/// (no-replay), and emits a content-addressed action record binding the `tool` invoked, the `cost`,
/// and the worker's `sub_task` (the receipt's audit payload). The executor admits this IFF the budget
/// gate holds (`spent_a + spent_b <= budget`), the epoch strictly advances, and the meters are
/// monotone — exactly the Lean dispatch gate. A worker that exceeds its mandate (over-budget) is
/// REFUSED here, in the fire path.
#[allow(clippy::too_many_arguments)]
pub fn build_worker_step_action(
    cipherclerk: &AppCipherclerk,
    board: CellId,
    worker: WorkerSlot,
    tool: Tool,
    prev_spent: u64,
    cost: u64,
    new_epoch: u64,
    sub_task: &str,
) -> Action {
    let new_spent = prev_spent.saturating_add(cost);
    let effects = vec![
        Effect::SetField {
            cell: board,
            index: worker.spend_slot() as usize,
            value: field_from_u64(new_spent),
        },
        Effect::SetField {
            cell: board,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(new_epoch),
        },
        Effect::EmitEvent {
            cell: board,
            event: Event::new(
                symbol(&format!("step/{}/{}", worker.label(), tool.label())),
                vec![
                    field_from_bytes(sub_task.as_bytes()),
                    field_from_u64(cost),
                    field_from_u64(new_epoch),
                ],
            ),
        },
    ];
    cipherclerk.make_action(board, "worker_step", effects)
}

// =============================================================================
// §4 — The DURABLE + AUDITABLE workflow engine.
//
// Modeled on `pg-dregg/src/workflow.rs` (`WorkflowEngine` / `run_durable` /
// `recover_from_durable` / `resume_durable` / the chain tooth), realized here on
// the in-process embedded executor with the real `TurnReceipt` chain as the
// durable log. (pg-dregg is a standalone workspace, not a member of this
// workspace, so it is the MODEL, not a dependency.)
// =============================================================================

/// One step of an orchestration: a worker, the tool it invokes, the cost it meters, and the sub-task it
/// is scoped to — the planned unit of work. The worker's [`Mandate`] (held in the [`OrchestrationEngine`])
/// must AUTHORIZE this step ([`Mandate::authorizes`]) or it is refused (in the fire path AND at audit).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct WorkStep {
    /// Which worker performs this step (also picks the board spend-meter).
    pub worker: WorkerSlot,
    /// The tool the worker invokes (must be in the worker's mandate's tool-set — the SCOPE check).
    pub tool: Tool,
    /// The computron cost this step meters against the worker's sub-budget + the swarm budget.
    pub cost: u64,
    /// The sub-task label (audit topic; the receipt binds it).
    pub sub_task: String,
}

impl WorkStep {
    /// A planned step.
    pub fn new(worker: WorkerSlot, tool: Tool, cost: u64, sub_task: &str) -> Self {
        Self {
            worker,
            tool,
            cost,
            sub_task: sub_task.to_string(),
        }
    }
}

/// A **durable log** of the orchestration's committed steps — the receipt chain that survives a crash,
/// plus the per-step record (worker, tool, cost, sub_task) the audit re-checks against the mandate.
/// This is the in-process analogue of `pg-dregg`'s `DurableLog` / `dregg.commit_log`: the receipt the
/// instant a step commits, appended; a crash leaves exactly the committed prefix; recovery rebuilds the
/// engine from this log alone, re-validating the chain on the way up.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct OrchestrationLog {
    /// The committed step records, in commit order (ordinal = index). Each pairs the planned
    /// [`WorkStep`] with the worker's spend meter AFTER the step (so the audit re-derives the running
    /// budget without replaying the executor).
    pub entries: Vec<LoggedStep>,
}

/// One committed step in the [`OrchestrationLog`]: the planned work, the worker's running spend after
/// it, and the verified [`TurnReceipt`] (the durable, chained proof the step committed).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct LoggedStep {
    /// The planned step (worker, tool, cost, sub_task).
    pub step: WorkStep,
    /// The worker's cumulative spend AFTER this step (the meter post-image; the audit re-derives the
    /// running mandate-budget from these without re-running the executor).
    pub spent_after: u64,
    /// The verified, CHAINED receipt — `previous_receipt_hash` links to the prior step (the open-board
    /// turn is ordinal-0's predecessor), so the pairwise window check over `[open] ++ receipts` audits
    /// the whole run and a tampered receipt breaks the chain.
    pub receipt: TurnReceipt,
}

impl OrchestrationLog {
    /// A fresh, empty durable log.
    pub fn new() -> Self {
        Self::default()
    }
    /// How many steps are durably committed.
    pub fn len(&self) -> usize {
        self.entries.len()
    }
    /// Whether no step is committed yet.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    /// The committed receipts in order — the chain the auditor verifies.
    pub fn receipts(&self) -> Vec<TurnReceipt> {
        self.entries.iter().map(|e| e.receipt.clone()).collect()
    }
}

/// The error a durable orchestration step can fail with — fail-closed, never silent.
#[derive(Clone, Debug)]
pub enum OrchestrationError {
    /// The step is OUT OF MANDATE per the off-ledger pre-check (a tool not in the worker's tool-set, or
    /// a spend that would breach the worker's sub-budget) — refused BEFORE submission, fail-closed.
    OutOfMandate {
        /// The worker whose mandate the step violates.
        worker: WorkerSlot,
        /// The tool the step requested.
        tool: Tool,
        /// Why (scope vs budget), as a legible string.
        why: String,
    },
    /// The verified executor REFUSED the turn (e.g. the `AffineLe` budget gate, the capability gate, or
    /// the no-replay epoch). The real, in-the-fire-path refusal — carries the executor's message.
    Refused(String),
}

impl std::fmt::Display for OrchestrationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OrchestrationError::OutOfMandate { worker, tool, why } => write!(
                f,
                "out-of-mandate: {} may not invoke {} — {why}",
                worker.label(),
                tool.label()
            ),
            OrchestrationError::Refused(e) => write!(f, "executor refused the worker turn: {e}"),
        }
    }
}

impl std::error::Error for OrchestrationError {}

/// A **durable, auditable orchestration engine**. It owns the embedded verified executor + the
/// coordinator board cell + the per-worker mandates, and drives each [`WorkStep`] as a verified turn
/// CHECKPOINTED to a durable log — crash-recoverable, exactly-once on resume. The receipt chain is the
/// audit trail ([`audit_run`]).
///
/// The engine borrows the executor; to model a "crash" the caller drops the engine and keeps the
/// [`OrchestrationLog`], then [`recover`] rebuilds the resumable state from the log ALONE (re-validating
/// the receipt chain on the way up — a log that does not chain is a corrupted store and is surfaced,
/// never silently resumed).
pub struct OrchestrationEngine<'a> {
    cipherclerk: &'a AppCipherclerk,
    exec: &'a EmbeddedExecutor,
    board: CellId,
    /// The coordinator's held mandate (the broad authority; every worker mandate must be `⊑` this).
    coordinator: Mandate,
    /// Per-worker conferred mandate (attenuated `⊑` the coordinator's) + running spend.
    worker_a: WorkerState,
    worker_b: WorkerState,
    /// The next epoch the next step must strictly advance to (no-replay).
    next_epoch: u64,
    /// The open-board receipt — the predecessor the first step's receipt chains onto. Carried so the
    /// audit verifies `[open] ++ steps` as ONE chain.
    open_receipt: Option<TurnReceipt>,
}

/// A worker's conferred mandate + its running cumulative spend (the engine's per-worker state).
#[derive(Clone, Debug)]
struct WorkerState {
    mandate: Mandate,
    spent: u64,
}

impl<'a> OrchestrationEngine<'a> {
    /// Construct an engine bound to a coordinator board cell, the coordinator's held mandate, and the
    /// two workers' attenuated mandates. **Panics in debug** if a worker mandate is NOT `⊑` the
    /// coordinator's — that would be an amplification, which the contract forbids (the Lean
    /// `worker_authority_subset_orchestrator` is the law; a caller building an amplifying engine is a
    /// programming error caught here, before any turn runs). Use [`Mandate::attenuate`] to derive
    /// worker mandates that are `⊑` by construction.
    pub fn new(
        cipherclerk: &'a AppCipherclerk,
        exec: &'a EmbeddedExecutor,
        board: CellId,
        coordinator: Mandate,
        worker_a_mandate: Mandate,
        worker_b_mandate: Mandate,
    ) -> Self {
        debug_assert!(
            worker_a_mandate.le(&coordinator),
            "worker-A mandate must be ⊑ the coordinator's (no amplification)"
        );
        debug_assert!(
            worker_b_mandate.le(&coordinator),
            "worker-B mandate must be ⊑ the coordinator's (no amplification)"
        );
        Self {
            cipherclerk,
            exec,
            board,
            coordinator,
            worker_a: WorkerState {
                mandate: worker_a_mandate,
                spent: 0,
            },
            worker_b: WorkerState {
                mandate: worker_b_mandate,
                spent: 0,
            },
            next_epoch: 2, // open-board advanced 0 -> 1; the first step goes 1 -> 2.
            open_receipt: None,
        }
    }

    fn worker_state(&self, w: WorkerSlot) -> &WorkerState {
        match w {
            WorkerSlot::A => &self.worker_a,
            WorkerSlot::B => &self.worker_b,
        }
    }
    fn worker_state_mut(&mut self, w: WorkerSlot) -> &mut WorkerState {
        match w {
            WorkerSlot::A => &mut self.worker_a,
            WorkerSlot::B => &mut self.worker_b,
        }
    }

    /// The coordinator's held mandate.
    pub fn coordinator(&self) -> &Mandate {
        &self.coordinator
    }
    /// A worker's conferred (attenuated) mandate.
    pub fn mandate_of(&self, w: WorkerSlot) -> &Mandate {
        &self.worker_state(w).mandate
    }
    /// A worker's running cumulative spend.
    pub fn spent(&self, w: WorkerSlot) -> u64 {
        self.worker_state(w).spent
    }

    /// **OPEN** the board: the coordinator pins `LEAD` + the swarm `BUDGET` and the meters/epoch. The
    /// resulting receipt is the chain's predecessor for the first step (carried for the audit).
    /// Idempotent: re-opening is a no-op once opened.
    pub fn open(&mut self, lead: &str) -> Result<TurnReceipt, OrchestrationError> {
        if let Some(r) = &self.open_receipt {
            return Ok(r.clone());
        }
        let action =
            build_open_board_action(self.cipherclerk, self.board, lead, self.coordinator.budget);
        let receipt = self
            .exec
            .submit_action(self.cipherclerk, action)
            .map_err(|e| OrchestrationError::Refused(e.to_string()))?;
        self.open_receipt = Some(receipt.clone());
        Ok(receipt)
    }

    /// **STEP** — run one [`WorkStep`] as a verified turn, checkpointing it to `log`. Fail-closed in
    /// TWO places that provably agree:
    ///   1. the off-ledger MANDATE pre-check ([`Mandate::authorizes`]) — a tool outside the worker's
    ///      tool-set or a spend over the worker's sub-budget is refused BEFORE submission
    ///      ([`OrchestrationError::OutOfMandate`]); the engine does not even build the turn;
    ///   2. the verified EXECUTOR — the `AffineLe` swarm-budget gate (+ monotone meters + no-replay
    ///      epoch) re-checks on commit; an over-swarm-budget step is REFUSED ([`OrchestrationError::Refused`]).
    ///
    /// On commit the receipt (chained onto the prior step / the open turn) is appended to `log`.
    pub fn step(
        &mut self,
        step: &WorkStep,
        log: &mut OrchestrationLog,
    ) -> Result<TurnReceipt, OrchestrationError> {
        let ws = self.worker_state(step.worker).clone();

        // (1) The off-ledger mandate pre-check — fail-closed BEFORE the turn runs.
        if !ws.mandate.tools.contains(&step.tool) {
            return Err(OrchestrationError::OutOfMandate {
                worker: step.worker,
                tool: step.tool,
                why: format!(
                    "tool {} not in granted scope {{{}}}",
                    step.tool.label(),
                    ws.mandate
                        .tools
                        .iter()
                        .map(|t| t.label())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            });
        }
        if !ws.mandate.authorizes(step.tool, ws.spent, step.cost) {
            return Err(OrchestrationError::OutOfMandate {
                worker: step.worker,
                tool: step.tool,
                why: format!(
                    "spend {}+{} would breach sub-budget {}",
                    ws.spent, step.cost, ws.mandate.budget
                ),
            });
        }

        // (2) The verified turn — the executor's AffineLe / monotone / no-replay gates re-check.
        let epoch = self.next_epoch;
        let action = build_worker_step_action(
            self.cipherclerk,
            self.board,
            step.worker,
            step.tool,
            ws.spent,
            step.cost,
            epoch,
            &step.sub_task,
        );
        let receipt = self
            .exec
            .submit_action(self.cipherclerk, action)
            .map_err(|e| OrchestrationError::Refused(e.to_string()))?;

        // Commit-side state advance (only on success — a refused step moves nothing).
        let new_spent = ws.spent.saturating_add(step.cost);
        self.worker_state_mut(step.worker).spent = new_spent;
        self.next_epoch = epoch + 1;
        log.entries.push(LoggedStep {
            step: step.clone(),
            spent_after: new_spent,
            receipt: receipt.clone(),
        });
        Ok(receipt)
    }

    /// **RUN** — drive a whole plan: open the board, then run each [`WorkStep`] in order, checkpointing
    /// each verified turn to `log`. Returns the count committed. A step refused (out-of-mandate or
    /// executor-refused) STOPS the run and is returned as the error — the durable log holds exactly the
    /// committed prefix (the crash-consistent shape).
    pub fn run(
        &mut self,
        lead: &str,
        plan: &[WorkStep],
        log: &mut OrchestrationLog,
    ) -> Result<usize, OrchestrationError> {
        self.open(lead)?;
        let mut committed = 0usize;
        for step in plan {
            self.step(step, log)?;
            committed += 1;
        }
        Ok(committed)
    }

    /// **RESUME** — finish a `plan` whose committed prefix is already in `log` (e.g. after a crash +
    /// [`recover`]). The committed steps are SKIPPED (the index-skip fast path), never re-applied;
    /// only the uncommitted TAIL is submitted. Returns `(skipped, committed)`. Exactly-once holds two
    /// ways that agree: the index-skip, and the executor's no-replay epoch (a stale re-submit of a
    /// committed step would not strictly advance the epoch and would be refused). The engine's
    /// `next_epoch` / spend meters must already be resumed (see [`OrchestrationEngine::resume_state`]).
    pub fn resume(
        &mut self,
        plan: &[WorkStep],
        log: &mut OrchestrationLog,
    ) -> Result<(usize, usize), OrchestrationError> {
        let skipped = log.len().min(plan.len());
        let tail = resume_plan(log, plan);
        let mut committed = 0usize;
        for step in tail {
            self.step(step, log)?;
            committed += 1;
        }
        Ok((skipped, committed))
    }

    /// Re-seat the engine's resumable state (per-worker spend + next epoch + open receipt) after a
    /// crash, from the [`RecoveredState`] [`recover`] produced + the surviving open receipt. After this
    /// the engine can [`OrchestrationEngine::resume`] the SAME plan exactly-once.
    pub fn resume_state(&mut self, recovered: RecoveredState, open_receipt: TurnReceipt) {
        self.worker_a.spent = recovered.spent_a;
        self.worker_b.spent = recovered.spent_b;
        self.next_epoch = recovered.next_epoch;
        self.open_receipt = Some(open_receipt);
    }

    /// The open-board receipt, if the board has been opened.
    pub fn open_receipt(&self) -> Option<&TurnReceipt> {
        self.open_receipt.as_ref()
    }
}

// =============================================================================
// §5 — RECOVERY (exactly-once) + AUDIT (the receipt chain proves no agent
// exceeded its mandate; a tampered or over-mandate step is detectable).
// =============================================================================

/// **RESUME PLAN** — given a durable `log` (the committed prefix) and the full `plan`, the steps still
/// to run (the uncommitted TAIL): `plan[log.len()..]`. The committed prefix is SKIPPED, never
/// re-applied — exactly-once. (The fast path; the backstop is the no-replay epoch, which would refuse a
/// stale re-submit of a committed step.) The Rust image of `pg-dregg`'s `resume_durable` index-skip.
pub fn resume_plan<'p>(log: &OrchestrationLog, plan: &'p [WorkStep]) -> &'p [WorkStep] {
    let done = log.len().min(plan.len());
    &plan[done..]
}

/// **RECOVER** — re-validate a durable `log` after a "crash" (the engine dropped; only the log
/// survived). Returns the worker spend-meters and the next epoch to resume at — rebuilt from the log
/// ALONE, re-validating the receipt chain on the way up. A log that does not chain is a corrupted store
/// and is surfaced as [`AuditError`], never silently resumed. The Rust image of `pg-dregg`'s
/// `recover_from_durable` (re-validate every persisted turn, resume from the head).
///
/// `open_receipt` is the open-board receipt that precedes the first step (the chain's genesis here);
/// pass it so the chain is validated as `[open] ++ steps`.
pub fn recover(
    open_receipt: &TurnReceipt,
    log: &OrchestrationLog,
) -> Result<RecoveredState, AuditError> {
    // Re-validate the receipt window `[open] ++ committed steps` — the self-checking store.
    let mut chain = Vec::with_capacity(log.len() + 1);
    chain.push(open_receipt.clone());
    chain.extend(log.receipts());
    verify_receipt_window(&chain).map_err(AuditError::ChainBroken)?;

    // Re-derive the per-worker running spend + the next epoch from the log post-images.
    let mut spent_a = 0u64;
    let mut spent_b = 0u64;
    for e in &log.entries {
        match e.step.worker {
            WorkerSlot::A => spent_a = e.spent_after,
            WorkerSlot::B => spent_b = e.spent_after,
        }
    }
    // open advanced 0 -> 1; each step advanced the epoch by 1, so the next epoch is 1 + len + 1.
    let next_epoch = 2 + log.len() as u64;
    Ok(RecoveredState {
        spent_a,
        spent_b,
        next_epoch,
    })
}

/// The state recovered from a durable log: the per-worker spend meters and the next epoch to resume at.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RecoveredState {
    /// Worker-A's cumulative spend, re-derived from the log.
    pub spent_a: u64,
    /// Worker-B's cumulative spend, re-derived from the log.
    pub spent_b: u64,
    /// The next epoch a resumed step must strictly advance to.
    pub next_epoch: u64,
}

/// Why an audit FAILED — each a concrete tamper / over-mandate detection, fail-closed.
#[derive(Clone, Debug)]
pub enum AuditError {
    /// The receipt chain does not link (a tampered, reordered, or substituted receipt) — caught by
    /// pairwise `dregg_turn::verify_receipt_extends`. The audit refuses CLOSED.
    ChainBroken(VerifyError),
    /// A step in the log EXCEEDED its worker's mandate (a tool outside the granted scope, or a running
    /// spend over the sub-budget) — the over-mandate detection. Carries the offending ordinal + why.
    OverMandate {
        /// The log ordinal (step index) that exceeded its mandate.
        ordinal: usize,
        /// Why (scope vs budget).
        why: String,
    },
    /// A worker mandate in the audited mandate-set is NOT `⊑` the coordinator's — an amplification that
    /// should never have been conferred. Caught structurally.
    AmplifiedMandate {
        /// The worker whose mandate amplifies.
        worker: WorkerSlot,
    },
}

impl std::fmt::Display for AuditError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AuditError::ChainBroken(e) => write!(f, "receipt chain broken (tamper): {e:?}"),
            AuditError::OverMandate { ordinal, why } => {
                write!(f, "step #{ordinal} exceeded its mandate: {why}")
            }
            AuditError::AmplifiedMandate { worker } => write!(
                f,
                "worker {} holds a mandate NOT ⊑ the coordinator's (amplification)",
                worker.label()
            ),
        }
    }
}

impl std::error::Error for AuditError {}

/// A clean audit verdict — the proof a light client gets back: the whole orchestration ran within
/// mandate, the receipt chain is intact, and conservation held.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuditOk {
    /// The number of committed steps audited.
    pub steps: usize,
    /// The final per-worker spend (re-derived from the chain).
    pub spent_a: u64,
    /// The final per-worker spend.
    pub spent_b: u64,
    /// The swarm budget the spend was bounded by (`spent_a + spent_b <= budget`).
    pub budget: u64,
    /// The chain head (the final receipt hash) — the commitment a light client pins.
    pub head: [u8; 32],
}

/// **AUDIT** — the headline. Given the open-board receipt, the durable log, the coordinator's held
/// mandate, and the per-worker conferred mandates, an AUDITOR (a light client that did NOT run the
/// orchestration) verifies that **no agent ever exceeded its mandate**. The audit:
///
///   1. **structural non-amplification** — every conferred worker mandate is `⊑` the coordinator's
///      ([`Mandate::le`], the Lean `worker_authority_subset_orchestrator`); an amplified mandate is
///      caught ([`AuditError::AmplifiedMandate`]) before any step is trusted;
///   2. **chain integrity** — pairwise `dregg_turn::verify_receipt_extends` over `[open] ++ step
///      receipts` — a tampered, reordered, or substituted receipt breaks the chain ([`AuditError::ChainBroken`]);
///   3. **per-step mandate re-check** — for each logged step, the auditor RE-DERIVES the worker's
///      running spend and re-checks [`Mandate::authorizes`]: a step whose tool is outside the worker's
///      granted scope, or whose running spend exceeds the sub-budget, is caught
///      ([`AuditError::OverMandate`]); the logged meter post-image must equal the re-derived value (the
///      meter cannot be forged);
///   4. **swarm-budget conservation** — `spent_a + spent_b <= coordinator.budget`, the affine bound the
///      executor's `AffineLe` gate enforced, re-checked over the audited totals.
///
/// A clean run returns [`AuditOk`] (the steps, the final spend, the chain head a light client pins). A
/// tampered or over-mandate run returns the concrete [`AuditError`]. This is the on-ledger TRUTH against
/// the loops' narration: a worker cannot CLAIM it stayed within mandate — the audit re-derives it.
pub fn audit_run(
    open_receipt: &TurnReceipt,
    log: &OrchestrationLog,
    coordinator: &Mandate,
    worker_a_mandate: &Mandate,
    worker_b_mandate: &Mandate,
) -> Result<AuditOk, AuditError> {
    // (1) Structural non-amplification: every conferred mandate ⊑ the coordinator's.
    if !worker_a_mandate.le(coordinator) {
        return Err(AuditError::AmplifiedMandate {
            worker: WorkerSlot::A,
        });
    }
    if !worker_b_mandate.le(coordinator) {
        return Err(AuditError::AmplifiedMandate {
            worker: WorkerSlot::B,
        });
    }

    // (2) Chain integrity over [open] ++ steps — a tampered receipt breaks this.
    let mut chain = Vec::with_capacity(log.len() + 1);
    chain.push(open_receipt.clone());
    chain.extend(log.receipts());
    verify_receipt_window(&chain).map_err(AuditError::ChainBroken)?;

    // (3) Per-step mandate re-check — re-derive each worker's running spend from the log.
    let mut spent_a = 0u64;
    let mut spent_b = 0u64;
    for (ordinal, e) in log.entries.iter().enumerate() {
        let (running, mandate) = match e.step.worker {
            WorkerSlot::A => (spent_a, worker_a_mandate),
            WorkerSlot::B => (spent_b, worker_b_mandate),
        };
        // The tool must be in the granted scope.
        if !mandate.tools.contains(&e.step.tool) {
            return Err(AuditError::OverMandate {
                ordinal,
                why: format!(
                    "{} invoked {} outside its granted scope",
                    e.step.worker.label(),
                    e.step.tool.label()
                ),
            });
        }
        // The running spend after this step must respect the sub-budget.
        if !mandate.authorizes(e.step.tool, running, e.step.cost) {
            return Err(AuditError::OverMandate {
                ordinal,
                why: format!(
                    "{} running spend {}+{} exceeds sub-budget {}",
                    e.step.worker.label(),
                    running,
                    e.step.cost,
                    mandate.budget
                ),
            });
        }
        // The logged post-image must equal the re-derived running spend (the meter cannot be forged).
        let derived = running.saturating_add(e.step.cost);
        if derived != e.spent_after {
            return Err(AuditError::OverMandate {
                ordinal,
                why: format!(
                    "{} logged spent_after {} disagrees with re-derived {}",
                    e.step.worker.label(),
                    e.spent_after,
                    derived
                ),
            });
        }
        match e.step.worker {
            WorkerSlot::A => spent_a = derived,
            WorkerSlot::B => spent_b = derived,
        }
    }

    // (4) Swarm-budget conservation: Σ worker spend <= the coordinator's budget.
    if spent_a.saturating_add(spent_b) > coordinator.budget {
        return Err(AuditError::OverMandate {
            ordinal: log.len(),
            why: format!(
                "Σ spend {} exceeds swarm budget {}",
                spent_a + spent_b,
                coordinator.budget
            ),
        });
    }

    let head = chain.last().map(|r| r.receipt_hash()).unwrap_or([0u8; 32]);
    Ok(AuditOk {
        steps: log.len(),
        spent_a,
        spent_b,
        budget: coordinator.budget,
        head,
    })
}

// =============================================================================
// §6 — StarbridgeAppContext mount.
// =============================================================================

/// The canonical web-constants module (slot layout + event topics + factory-vk hex).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("agent-orchestration")
        .slot("LEAD_SLOT", LEAD_SLOT as u64)
        .slot("BUDGET_SLOT", BUDGET_SLOT as u64)
        .slot("SPENT_A_SLOT", SPENT_A_SLOT as u64)
        .slot("SPENT_B_SLOT", SPENT_B_SLOT as u64)
        .slot("EPOCH_SLOT", EPOCH_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&ORCHESTRATION_FACTORY_VK))
        .topic("BOARD_OPENED", "orchestration-board-opened")
}

/// Register the agent-orchestration starbridge-app on a shared context.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(orchestration_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "orchestration-board".into(),
        descriptor: serde_json::json!({
            "component": "dregg-orchestration-board",
            "module": "/starbridge-apps/agent-orchestration/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["lead", "budget", "spent_a", "spent_b", "epoch"],
            "slot_layout": {
                "lead": LEAD_SLOT,
                "budget": BUDGET_SLOT,
                "spent_a": SPENT_A_SLOT,
                "spent_b": SPENT_B_SLOT,
                "epoch": EPOCH_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&coordinator_child_program_vk()),
            "methods": ["open_board", "worker_step"],
        }),
    });

    factory_vk
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization};

    fn cclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x5au8; 32])
    }
    fn cell() -> CellId {
        CellId::from_bytes([7u8; 32])
    }

    // ── §1 the mandate lattice: granted ⊑ held + attenuate never widens ──────

    #[test]
    fn coordinator_mandate_holds_the_broad_toolset() {
        let coord = Mandate::coordinator([Tool::Read, Tool::Search, Tool::Write], 1000, "task");
        assert!(coord.tools.contains(&Tool::Write));
        assert_eq!(coord.budget, 1000);
    }

    #[test]
    fn attenuate_narrows_tools_and_clamps_budget() {
        let coord = Mandate::coordinator([Tool::Read, Tool::Search, Tool::Write], 1000, "task");
        // Request Read+Search+Spend with a 600 budget; Spend is NOT held ⇒ dropped; budget fits.
        let w = coord.attenuate([Tool::Read, Tool::Search, Tool::Spend], 600, "sub");
        assert_eq!(
            w.tools,
            BTreeSet::from([Tool::Read, Tool::Search]),
            "Spend (not held) is dropped by intersection"
        );
        assert_eq!(w.budget, 600);
        assert!(w.le(&coord), "the attenuation is ⊑ the coordinator's");
    }

    #[test]
    fn attenuate_clamps_overbudget_request_down() {
        let coord = Mandate::coordinator([Tool::Read], 500, "task");
        // Request MORE budget than held — clamped down to 500 (no amplification).
        let w = coord.attenuate([Tool::Read], 9999, "sub");
        assert_eq!(w.budget, 500, "an over-budget request is clamped to held");
        assert!(w.le(&coord));
    }

    #[test]
    fn le_is_the_subset_and_budget_order() {
        let held = Mandate::coordinator([Tool::Read, Tool::Write], 1000, "t");
        let ok = Mandate::coordinator([Tool::Read], 400, "s");
        assert!(ok.le(&held));
        // a WIDER tool is not ⊑.
        let wider = Mandate::coordinator([Tool::Read, Tool::Write, Tool::Spend], 400, "s");
        assert!(
            !wider.le(&held),
            "a tool not held breaks ⊑ (no amplification)"
        );
        // a LARGER budget is not ⊑.
        let richer = Mandate::coordinator([Tool::Read], 1001, "s");
        assert!(!richer.le(&held), "a larger budget breaks ⊑");
    }

    #[test]
    fn strict_attenuation_drops_a_held_tool() {
        // The Lean `worker_attenuation_is_strict`: the coordinator holds Write, the worker does not.
        let coord = Mandate::coordinator([Tool::Read, Tool::Write], 1000, "t");
        let worker = coord.attenuate([Tool::Read], 400, "s");
        assert!(worker.le(&coord));
        assert!(coord.tools.contains(&Tool::Write));
        assert!(
            !worker.tools.contains(&Tool::Write),
            "the subset is STRICT — Write is dropped"
        );
    }

    #[test]
    fn authorizes_is_scope_and_budget_fail_closed() {
        let m = Mandate::coordinator([Tool::Read, Tool::Search], 1000, "t");
        assert!(m.authorizes(Tool::Read, 0, 600)); // in scope, fits
        assert!(m.authorizes(Tool::Search, 600, 400)); // 600+400=1000 <= 1000 (at ceiling)
        assert!(!m.authorizes(Tool::Search, 600, 401)); // over budget — BUDGET tooth
        assert!(!m.authorizes(Tool::Write, 0, 1)); // out of scope — SCOPE tooth
    }

    // ── §2 the coordinator program mirrors the Lean dispatch constraints ─────

    #[test]
    fn coordinator_program_has_the_budget_policy_clauses() {
        let CellProgram::Predicate(ks) = coordinator_program() else {
            panic!("coordinator program must be a flat Predicate");
        };
        assert_eq!(ks, coordinator_constraints());
        assert!(
            ks.iter().any(|k| matches!(
                k,
                StateConstraint::AffineLe { terms, c: 0 }
                    if terms.contains(&(1, SPENT_A_SLOT))
                        && terms.contains(&(1, SPENT_B_SLOT))
                        && terms.contains(&(-1, BUDGET_SLOT))
            )),
            "the budget gate spent_a + spent_b <= budget must be a clause"
        );
        assert!(
            ks.iter().any(
                |k| matches!(k, StateConstraint::WriteOnce { index } if *index == BUDGET_SLOT)
            )
        );
        assert!(ks.iter().any(
            |k| matches!(k, StateConstraint::StrictMonotonic { index } if *index == EPOCH_SLOT)
        ));
    }

    // ── §3 turn builders carry real effects + a real signature ───────────────

    #[test]
    fn worker_step_action_advances_meter_epoch_and_records() {
        let cc = cclerk();
        let action =
            build_worker_step_action(&cc, cell(), WorkerSlot::A, Tool::Search, 0, 300, 2, "index");
        // spent_a := 300, epoch := 2, + the action record event.
        assert_eq!(action.effects.len(), 3);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. }
                if *index == SPENT_A_SLOT as usize && *value == field_from_u64(300)
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, value, .. }
                if *index == EPOCH_SLOT as usize && *value == field_from_u64(2)
        ));
    }

    #[test]
    fn worker_step_action_carries_a_real_signature() {
        let cc = cclerk();
        let action = build_worker_step_action(&cc, cell(), WorkerSlot::B, Tool::Read, 0, 1, 2, "t");
        match action.authorization {
            Authorization::Signature(a, b) => assert!(a != [0u8; 32] || b != [0u8; 32]),
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    // ── §5 resume_plan skips the committed prefix (exactly-once index-skip) ───

    #[test]
    fn resume_plan_returns_only_the_uncommitted_tail() {
        let plan = vec![
            WorkStep::new(WorkerSlot::A, Tool::Search, 100, "a"),
            WorkStep::new(WorkerSlot::B, Tool::Read, 100, "b"),
            WorkStep::new(WorkerSlot::A, Tool::Summarize, 100, "c"),
        ];
        let log = OrchestrationLog::new();
        // nothing committed ⇒ the whole plan is the tail.
        assert_eq!(resume_plan(&log, &plan).len(), 3);
        // and a plan whose prefix is all-consumed yields an empty tail.
        assert_eq!(resume_plan(&log, &plan[..0]).len(), 0);
    }

    // ── §6 register installs the factory + inspector ─────────────────────────

    #[test]
    fn register_installs_factory_and_inspector() {
        let cc = cclerk();
        let executor = EmbeddedExecutor::new(&cc, "default");
        let ctx = StarbridgeAppContext::new(cc, executor);
        let vk = register(&ctx);
        assert_eq!(vk, ORCHESTRATION_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(
            ctx.inspector_registry()
                .get("orchestration-board")
                .is_some()
        );
    }
}
