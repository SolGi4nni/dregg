# durable-workflow

**A crash-resumable, exactly-once, metered durable-execution engine — DBOS-style
durable workflows with a pluggable step executor, over a durable store.**

A workflow is *deterministic coordination*: it decides what to do next only from
results it already has. The side effects live in **steps**, which run at-most-once
per logical position and whose results are checkpointed to a durable
[`duroxide`](https://crates.io/crates/duroxide) store. On restart the runtime
replays the recorded history — a completed step returns its recorded result without
re-running, and execution resumes from the first unfinished step. A crash
mid-workflow therefore resumes **exactly-once** from the last checkpoint.

## What is here

| item | where | what it is |
|---|---|---|
| `WorkloadRun` / `WorkloadSpec` | `src/lib.rs`, `src/runner.rs` | an ordered list of steps run as durable, exactly-once-metered units |
| `StepRunner` (trait) | `src/runner.rs` | the **pluggable executor seam** — one method, `run(spec) -> value`. A production runner drives a wasm sandbox / OCI container / microVM behind it; the checkpoint/resume/meter machinery is unchanged |
| `ExprRunner` | `src/runner.rs` | the bundled deterministic runner (a tiny `expr`/`echo` interpreter) so the engine is complete + testable with no external executor |
| `run_workflow_on_disk` | `src/lib.rs` | the persistent path — checkpoints to an on-disk WAL-durable SQLite store; a crashed instance resumes exactly-once on a fresh process |
| `MeterBackend` / `lease_budget_admits` | `src/meter.rs` | where a step's charge lands (in-process tally, or the shared `hosted_meter` outbox) + the replenishing-lease admission gate |
| `deploy::*` | `src/deploy.rs` (feature `deploy`) | the launchpad seam: a launch = a durable metered workflow **plus** a content-addressed landing page + token metadata over IPFS |

## The exactly-once + metered guarantee

Each durable step schedules a `MeterTick` charging its period against the lease.
Because the tick is a durable activity, it runs at-most-once per logical step and
replays a checkpointed result without re-running — so each period charges **exactly
once**, even across a crash + resume. The orchestration gates each step's charge
against the budget *before* scheduling it: an over-budget step fails the workflow
before any work runs or any charge commits (lease lapse → reap). `tests/crash_resume.rs`
proves all three: run-to-completion metered, exactly-once resume after a crash (step
does not re-execute, meter is not doubled), and over-budget reap-before-run.

## How it composes with settlement (the WELD)

The `pg` feature's meter backend writes the **same** `hosted_meter` outbox that
`hosted-durable`'s conserving settlement rail reads — reusing that crate's outbox
writer verbatim, not a second copy. So the charges this engine records are exactly
the rows a conserving `Effect::Transfer` settles: durable metering and durable
settlement meet on one idempotent `(lease_id, period)` table. This crate owns the
*execution* half (`hosted-durable` explicitly named the durable workflow runtime as
its follow-up); together they are the metered durable-execution stack.

## The launchpad seam (feature `deploy`)

A launch is two things at once, made one receipt:

1. a **durable, metered build/deploy workflow** (the rest of this crate); and
2. a **content-addressed microsite** (the landing page a launch gets) + **content-
   addressed token metadata/image** — every asset pinned to IPFS, its address a
   blake3 CIDv1 anyone re-witnesses against the bytes (`dregg-ipfs`).

`pin_launch_content` pins the page, its assets, the token image, and assembles token
metadata JSON that references the image by `ipfs://<cid>` — the whole launch content-
addressed end to end. `deploy_launch` additionally runs the durable metered workflow,
returning a `LaunchReceipt` with both halves. `tests/deploy.rs` proves the content
re-witnesses against its CIDs, is deterministic (idempotent launches), refuses a
tampered fetch, and composes with a real durable workflow.

## Durability boundary (honest)

Durability is exactly the durability of the store. The on-disk store is single-host,
WAL-durable SQLite: it survives process crash and restart on the **same host**, not
host loss. Multi-region / replicated durability is a property of a different store
(a replicated Postgres provider); swapping the store does not change a line of the
workflow. The `ExprRunner` is a deterministic stand-in, not a general compute
sandbox — a production deployment plugs a real isolate in behind `StepRunner`.

## Build + test

```sh
cargo test                       # engine + crash-resume (in-process meter, SQLite store)
cargo test --features deploy     # + the launchpad/IPFS content-addressing seam
cargo build --features pg        # + the shared hosted_meter outbox backend (DB-gated)
```
