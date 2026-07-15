//! `durable-workflow` — a crash-resumable, exactly-once, metered durable-execution
//! engine.
//!
//! ## The model (DBOS / Durable-Task / Temporal lineage)
//!
//! A **workflow** is *deterministic coordination*: it only decides what to do next
//! from results it already has. The side effects live in **steps**, which run **at
//! most once per logical position** and whose results are durably checkpointed to a
//! [`duroxide`] `Provider` store. On restart the runtime **replays** the recorded
//! history: a completed step returns its recorded result *without re-running*, and
//! execution resumes from the first unfinished step. That replay is the durability
//! guarantee — a crash mid-workflow resumes **exactly-once** from the last
//! checkpoint.
//!
//! A durable workload here is:
//! - a [`WorkloadRun`] — an ordered list of [`WorkloadSpec`] steps — run under the
//!   [`ORCHESTRATION_WORKLOAD_RUN`] orchestration;
//! - each step is a [`ACTIVITY_RUN_WORKLOAD`] activity that invokes the injected
//!   [`StepRunner`] (the pluggable executor seam — wasm, OCI, microVM, or the
//!   bundled deterministic [`ExprRunner`]);
//! - paired with a [`ACTIVITY_METER_TICK`] activity that charges the lease meter —
//!   the transactional twin of the work: a step's effect and its charge are both
//!   durable history, recovered together-or-not on replay.
//!
//! ## Map to a funded lease
//!
//! A funded execution-lease authorizes a workflow. [`WorkloadRun`] carries the
//! lease `budget_units`; the orchestration gates each step's charge against it
//! **before** scheduling the tick ([`lease_budget_admits`]) — a step whose charge
//! would exceed the budget fails the workflow *before any charge commits* (the
//! lease has lapsed → the workload is reaped, never run-and-not-paid). Because the
//! ticks are durable, crash-recovery resumes within the same budget — re-running
//! never double-charges, and an exhausted workflow stays failed across restarts.
//!
//! The charge lands in one of two backends ([`MeterBackend`]): an in-process tally
//! (default), or the Postgres `hosted_meter` transactional outbox (feature `pg`)
//! that the `hosted-durable` conserving settlement rail reads — so durable metering
//! and durable settlement meet on one idempotent table.
//!
//! ## Durability boundary (honest)
//!
//! Durability is exactly the durability of the `Provider` store. The on-disk store
//! ([`run_workflow_on_disk`]) is single-host, WAL-durable SQLite: it survives
//! process crash and restart on the **same host**, not host loss. Multi-region /
//! replicated durability is a property of a different store (a replicated Postgres
//! provider); swapping the store does not change a line of the workflow.

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

pub mod meter;
pub mod runner;

#[cfg(feature = "deploy")]
pub mod deploy;

pub use meter::{lease_budget_admits, metrics, MeterBackend, MeterCharge};
pub use runner::{ExprRunner, StepRunner, WorkloadSpec};

/// The orchestration name the general workload runner registers under: an arbitrary
/// ordered list of [`WorkloadSpec`] steps run as durable, exactly-once-metered units.
pub const ORCHESTRATION_WORKLOAD_RUN: &str = "WorkloadRun";

/// The activity that runs one workload step through the injected [`StepRunner`].
pub const ACTIVITY_RUN_WORKLOAD: &str = "RunWorkload";

/// The activity that charges the lease meter for one step (the transactional twin).
pub const ACTIVITY_METER_TICK: &str = "MeterTick";

/// The shared settlement-outbox table the `pg` meter backend writes and the
/// `hosted-durable` conserving settlement rail reads (kept equal to
/// `hosted_durable::METER_TABLE`).
pub const METER_TABLE: &str = "hosted_meter";

/// The input to the durable workflow: an ordered list of steps, each run as its own
/// durable, checkpointed, exactly-once-metered unit.
///
/// Any workload runs through it — an agent-served request as a one-step run, a build
/// or batch job as an N-step one. Each step charges `cost_per_step` against
/// `budget_units`; a step whose charge would exceed the budget fails the workflow
/// (lease lapse → reap) *before that step runs*.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkloadRun {
    /// The execution-lease budget, in meter units.
    pub budget_units: i64,
    /// Meter cost charged per step.
    pub cost_per_step: i64,
    /// The workload steps to run durably, in order.
    pub steps: Vec<WorkloadSpec>,
    /// Park on `pause_event` after this step ordinal (1-based) is durably
    /// checkpointed + metered, before the next step runs — the deterministic
    /// crash/pause point the recovery proof drives. `None` runs straight through.
    #[serde(default)]
    pub pause_after_step: Option<usize>,
    /// The external event the orchestration parks on at the pause point. Production
    /// runs leave it `None`.
    #[serde(default)]
    pub pause_event: Option<String>,
}

impl WorkloadRun {
    /// A straight run-to-completion of `steps`, charged `cost_per_step` against
    /// `budget_units`, with no pause point.
    pub fn new(budget_units: i64, cost_per_step: i64, steps: Vec<WorkloadSpec>) -> WorkloadRun {
        WorkloadRun {
            budget_units,
            cost_per_step,
            steps,
            pause_after_step: None,
            pause_event: None,
        }
    }

    /// Park on `event` after step `after` (1-based) is durably checkpointed +
    /// metered — the deterministic crash/pause point for a recovery proof.
    pub fn with_pause(mut self, after: usize, event: impl Into<String>) -> WorkloadRun {
        self.pause_after_step = Some(after);
        self.pause_event = Some(event.into());
        self
    }
}

/// The terminal result of a durable workflow.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct WorkflowOutput {
    /// Each durable step's output value, in order.
    pub outputs: Vec<String>,
    /// Total meter units charged against the lease across the workflow.
    pub meter_units: i64,
}

// ---------------------------------------------------------------------------
// Registry construction.
// ---------------------------------------------------------------------------

/// Build the duroxide registries (activities + orchestration) for the durable
/// workload runner, driving steps through `runner` and charging into `backend`.
/// Register these with a `duroxide` runtime over any `Provider` store.
///
/// `runner` is `Arc<dyn StepRunner>` (or any `Arc<R: StepRunner>`): the pluggable
/// executor. `backend` selects the meter sink ([`MeterBackend::InProcess`] or, with
/// feature `pg`, the shared `hosted_meter` outbox).
pub fn build_registries(
    runner: Arc<dyn StepRunner>,
    backend: MeterBackend,
) -> (
    duroxide::runtime::registry::ActivityRegistry,
    duroxide::OrchestrationRegistry,
) {
    use duroxide::runtime::registry::ActivityRegistry;
    use duroxide::{OrchestrationContext, OrchestrationRegistry};

    let activities = ActivityRegistry::builder()
        // RunWorkload: decode a spec, run it through the injected StepRunner,
        // return its value. Offloaded to a blocking thread (we are inside duroxide's
        // tokio runtime; a runner may block on a real isolate).
        .register(ACTIVITY_RUN_WORKLOAD, {
            let runner = runner.clone();
            move |ctx: duroxide::ActivityContext, input: String| {
                let runner = runner.clone();
                async move {
                    let instance = ctx.instance_id().to_string();
                    let spec: WorkloadSpec = serde_json::from_str(&input)
                        .map_err(|e| format!("RunWorkload: bad spec: {e}"))?;
                    let label = spec.label.clone();
                    let value = tokio::task::spawn_blocking(move || runner.run(&spec))
                        .await
                        .map_err(|e| format!("RunWorkload: join error: {e}"))?
                        .map_err(|e| format!("RunWorkload: {e}"))?;
                    // Count the REAL execution (not the replayed return) so
                    // exactly-once is observable.
                    metrics::add(&instance, &format!("run:{label}"), 1);
                    Ok(value)
                }
            }
        })
        // MeterTick: charge `amount` units for `period` against this lease (= the
        // workflow instance), returning the running total. The single seam where the
        // charge lands — the in-process tally or the shared Postgres outbox.
        .register(ACTIVITY_METER_TICK, {
            move |ctx: duroxide::ActivityContext, input: String| {
                let backend = backend.clone();
                async move {
                    let lease_id = ctx.instance_id().to_string();
                    let charge: MeterCharge = serde_json::from_str(&input)
                        .map_err(|e| format!("MeterTick: bad charge: {e}"))?;
                    let total = backend.charge(&lease_id, charge).await?;
                    Ok(total.to_string())
                }
            }
        })
        .build();

    let orchestrations = OrchestrationRegistry::builder()
        // The general workload runner: an arbitrary list of steps run durably. Each
        // step gates its charge BEFORE running (an exhausted lease reaps the step
        // rather than running-and-not-paying), runs through the StepRunner, then
        // meters — so every step is its own checkpointed, exactly-once, metered
        // durable unit.
        .register(
            ORCHESTRATION_WORKLOAD_RUN,
            |ctx: OrchestrationContext, input: String| async move {
                let cfg: WorkloadRun =
                    serde_json::from_str(&input).map_err(|e| format!("bad WorkloadRun: {e}"))?;

                let mut total: i64 = 0;
                let mut outputs: Vec<String> = Vec::with_capacity(cfg.steps.len());
                for (i, spec) in cfg.steps.iter().enumerate() {
                    let period = (i as i64) + 1;
                    // Replenishing-lease admission (pure / deterministic ⇒
                    // replay-safe inside the orchestration).
                    if !lease_budget_admits(cfg.budget_units, cfg.cost_per_step, period) {
                        let projected = total + cfg.cost_per_step;
                        return Err(format!(
                            "execution-lease exhausted: step {period} charge would reach \
                             {projected} > budget {}",
                            cfg.budget_units
                        ));
                    }
                    let spec_json = serde_json::to_string(spec).map_err(|e| e.to_string())?;
                    let value = ctx
                        .schedule_activity(ACTIVITY_RUN_WORKLOAD, spec_json)
                        .await?;

                    let charge = serde_json::to_string(&MeterCharge {
                        period,
                        amount: cfg.cost_per_step,
                    })
                    .map_err(|e| e.to_string())?;
                    total = ctx
                        .schedule_activity(ACTIVITY_METER_TICK, charge)
                        .await?
                        .parse()
                        .map_err(|e| format!("meter total: {e}"))?;
                    outputs.push(value);

                    // Deterministic crash/pause point (recovery proof only): park
                    // after this step is durably checkpointed + metered.
                    if cfg.pause_after_step == Some(period as usize) {
                        if let Some(ev) = cfg.pause_event.as_ref() {
                            let _ = ctx.schedule_wait(ev).await;
                        }
                    }
                }
                let out = WorkflowOutput {
                    outputs,
                    meter_units: total,
                };
                serde_json::to_string(&out).map_err(|e| e.to_string())
            },
        )
        .build();

    (activities, orchestrations)
}

// ---------------------------------------------------------------------------
// One-shot durable runners.
// ---------------------------------------------------------------------------

/// Run a [`WorkloadRun`] to completion over an **in-memory** SQLite durable store,
/// blocking until it finishes, driving steps through `runner`. The store is
/// process-local — it proves the request→durable→metered weld end to end but does
/// NOT survive the process. For the crash-resume-across-a-restart guarantee use
/// [`run_workflow_on_disk_blocking`].
///
/// Must NOT be called from inside an existing tokio runtime (it builds its own).
#[cfg(feature = "sqlite")]
pub fn run_workflow_in_memory_blocking(
    input: &WorkloadRun,
    instance: &str,
    runner: Arc<dyn StepRunner>,
) -> Result<WorkflowOutput, String> {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|e| format!("durable: tokio runtime build failed: {e}"))?;
    rt.block_on(run_workflow_in_memory(input, instance, runner))
}

/// The async core of [`run_workflow_in_memory_blocking`].
#[cfg(feature = "sqlite")]
pub async fn run_workflow_in_memory(
    input: &WorkloadRun,
    instance: &str,
    runner: Arc<dyn StepRunner>,
) -> Result<WorkflowOutput, String> {
    use duroxide::providers::sqlite::SqliteProvider;
    use duroxide::runtime::Runtime;
    use duroxide::Client;
    use std::time::Duration;

    let store = Arc::new(
        SqliteProvider::new_in_memory()
            .await
            .map_err(|e| format!("durable: open in-memory store: {e}"))?,
    );
    let input_json = serde_json::to_string(input).map_err(|e| e.to_string())?;
    let (activities, orchestrations) = build_registries(runner, MeterBackend::InProcess);
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    let result = async {
        client
            .start_orchestration(instance, ORCHESTRATION_WORKLOAD_RUN, input_json)
            .await
            .map_err(|e| format!("durable: start orchestration: {e}"))?;
        let status = client
            .wait_for_orchestration(instance, Duration::from_secs(30))
            .await
            .map_err(|e| format!("durable: await orchestration: {e}"))?;
        decode_status(status)
    }
    .await;

    rt.shutdown(None).await;
    result
}

/// Run a [`WorkloadRun`] to completion over an **on-disk** SQLite durable store at
/// `db_path`, blocking until it finishes, driving steps through `runner`.
///
/// This is the persistent path: the workflow's checkpoints are written to `db_path`.
/// If the **process** crashes mid-workflow, the instance survives on disk and a fresh
/// process resumes it from the last checkpoint, exactly-once — a completed step's
/// recorded result is replayed (never re-executed) and the meter is never
/// double-charged.
///
/// `db_path`'s parent directory is created if needed. The store is single-host,
/// WAL-durable SQLite — it survives process crash + restart on the **same host**, not
/// host loss. Calling this with an `instance` already present in the store is the
/// recovery path: the runtime auto-resumes the in-flight instance and this call
/// awaits its completion, so the function is safe as both the first run and the
/// post-crash recovery of the same request.
///
/// Must NOT be called from inside an existing tokio runtime (it builds its own).
#[cfg(feature = "sqlite")]
pub fn run_workflow_on_disk_blocking(
    input: &WorkloadRun,
    instance: &str,
    db_path: &std::path::Path,
    runner: Arc<dyn StepRunner>,
) -> Result<WorkflowOutput, String> {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|e| format!("durable: tokio runtime build failed: {e}"))?;
    rt.block_on(run_workflow_on_disk(input, instance, db_path, runner))
}

/// The async core of [`run_workflow_on_disk_blocking`]: open (or create) the on-disk
/// store at `db_path`, run/resume `instance`, and return its output.
#[cfg(feature = "sqlite")]
pub async fn run_workflow_on_disk(
    input: &WorkloadRun,
    instance: &str,
    db_path: &std::path::Path,
    runner: Arc<dyn StepRunner>,
) -> Result<WorkflowOutput, String> {
    use duroxide::providers::sqlite::SqliteProvider;
    use duroxide::runtime::Runtime;
    use duroxide::{Client, OrchestrationStatus};
    use std::time::Duration;

    if let Some(parent) = db_path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)
                .map_err(|e| format!("durable: create store dir {}: {e}", parent.display()))?;
        }
    }
    let db_url = format!("sqlite:{}?mode=rwc", db_path.display());
    let store = Arc::new(
        SqliteProvider::new(&db_url, None)
            .await
            .map_err(|e| format!("durable: open on-disk store {}: {e}", db_path.display()))?,
    );
    let input_json = serde_json::to_string(input).map_err(|e| e.to_string())?;
    let (activities, orchestrations) = build_registries(runner, MeterBackend::InProcess);
    let rt = Runtime::start_with_store(store.clone(), activities, orchestrations).await;
    let client = Client::new(store.clone());

    let result = async {
        // Start only if this instance is not already on disk. A present instance is a
        // request that crashed mid-flight; the runtime started above auto-resumes it,
        // so we must NOT re-start (that would reject) — just await its completion.
        let present = matches!(
            client.get_orchestration_status(instance).await,
            Ok(s) if !matches!(s, OrchestrationStatus::NotFound)
        );
        if !present {
            client
                .start_orchestration(instance, ORCHESTRATION_WORKLOAD_RUN, input_json)
                .await
                .map_err(|e| format!("durable: start orchestration: {e}"))?;
        }
        // On-disk SQLite serializes writers; under contention duroxide backs off and
        // retries locked writes. Wait long enough that a progressing workflow is not
        // declared failed prematurely.
        let status = client
            .wait_for_orchestration(instance, Duration::from_secs(60))
            .await
            .map_err(|e| format!("durable: await orchestration: {e}"))?;
        decode_status(status)
    }
    .await;

    rt.shutdown(None).await;
    result
}

/// Decode a terminal orchestration status into a [`WorkflowOutput`] or an error.
#[cfg(feature = "sqlite")]
fn decode_status(status: duroxide::OrchestrationStatus) -> Result<WorkflowOutput, String> {
    use duroxide::OrchestrationStatus;
    match status {
        OrchestrationStatus::Completed { output, .. } => {
            serde_json::from_str(&output).map_err(|e| format!("durable: decode output: {e}"))
        }
        OrchestrationStatus::Failed { details, .. } => Err(details.display_message()),
        other => Err(format!("durable: unexpected status: {other:?}")),
    }
}

/// A convenience wrapper: run a `WorkloadRun` on disk with the bundled deterministic
/// [`ExprRunner`] and the in-process meter. The zero-dependency-executor path an
/// integration test or a self-contained demo uses.
#[cfg(feature = "sqlite")]
pub fn run_expr_workflow_on_disk(
    input: &WorkloadRun,
    instance: &str,
    db_path: &std::path::Path,
) -> Result<WorkflowOutput, String> {
    run_workflow_on_disk_blocking(input, instance, db_path, Arc::new(ExprRunner))
}
