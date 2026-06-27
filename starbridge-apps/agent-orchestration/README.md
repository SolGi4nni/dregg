# starbridge-agent-orchestration

**Verifiable DURABLE + AUDITABLE multi-agent orchestration — every worker action is a cap-gated verified turn, the whole run is a crash-recoverable workflow, and an auditor re-derives it from the receipt chain and is never fooled.**

A **COORDINATOR** dispatch-board cell holds a task + a conserved budget and issues each **WORKER**
an **ATTENUATED MANDATE** (a scope-narrowed tool-set ∧ a sub-budget ∧ a sub-task — strictly weaker
than the coordinator holds: `granted ⊑ held`, the proven non-amplification). Every worker step is a
verified turn the executor re-enforces the budget policy on; the run is checkpointed to a receipt log
(crash-recoverable, exactly-once on resume); and the receipt chain is the audit trail. A worker that
reaches for a wider tool, an over-budget spend, or a replayed step is **REFUSED, fail-closed, in the
fire path** — and an auditor (a light client) re-derives the run and proves no agent ever exceeded its
mandate.

It is the **durable + auditable twin of `swarm-orchestration`** (the in-memory shape): the SAME slot
layout and the SAME canonical `coordinator_program()` (`AffineLe(spent_a + spent_b <= budget)` +
`WriteOnce(LEAD/BUDGET)` + `Monotonic(SPENT_*)` + `StrictMonotonic(EPOCH)`), wrapped in a durable
workflow engine whose receipt chain survives a crash.

## The axes (the unified template)

| Axis | What it is | Where | Test |
|---|---|---|---|
| **1. Verified core** | a `FactoryDescriptor` + `coordinator_program()` whose slot-caveats ARE the budget policy; the executor refuses any over-budget / replayed / rolled-back turn | `src/lib.rs` | `src/lib.rs::tests`, `tests/orchestration_teeth.rs` |
| **2. deos surface** | the board composed as a `DeosApp` — per-viewer projection on the auditor ⊂ worker ⊂ coordinator ladder, the gated `worker_step` htmx tooth, web-of-cells publish, manifest | `src/deos.rs` | `tests/deos_surface.rs` |
| **3. Service cell** | a typed `InterfaceDescriptor` driven through the `invoke()` front door — the orchestration as named methods (cells-as-service-objects) | `src/service.rs` | `tests/service.rs` |
| **4. deos-view card** | the UI as a renderer-independent `deos.ui.*` view-tree (native gpui / web HTML / discord — one piece of data) | `src/card.rs` | `src/card.rs::tests` |
| **5. Reactor** | the autonomous COORDINATOR agent-loop as a `Reactor` (the reactive twin of `invoke()`): watch a posted mandate, react by auto-dispatching the first worker step within the budget | `src/reactor.rs` | `src/reactor.rs::tests` |

These compose: AX2/AX3/AX5 all install/assume the SAME `coordinator_program()` AX1 bakes, so the
budget gate + meters + epoch caveats bite identically whether a turn arrives as a raw
`build_*_action`, a gated `DeosApp` fire, an `invoke()` method call, or an autonomous reaction.
Soundness lives in the verified core (axis 1); the rest are faces onto it.

Two further surfaces ride the same primitive (not template axes, but real faces this app needs):

- **`src/durable.rs` + the engine in `src/lib.rs`** — the run as a pg-dregg-shaped DURABLE WORKFLOW:
  `OrchestrationEngine` drives each `WorkStep` as a verified turn checkpointed to an `OrchestrationLog`
  (crash-recoverable, exactly-once on `resume`), and `audit_run` re-derives the whole run from the
  receipt chain (chain integrity via `verify_receipt_extends` + a per-step mandate re-check + the
  swarm-budget conservation check). A tampered receipt or an over-mandate step is DETECTABLE.
- **`src/mcp.rs`** — the live MCP binding: an agent loop's `tools/call` is classified to a
  `(Tool, cost)` and run AS a verified `WorkStep`, so the receipt content-addresses the exact tool +
  arguments and a call outside the worker's mandate is refused in the fire path.

## Axis 1 — the budget policy, enforced by caveats (not asserted)

The coordinator board cell carries `coordinator_program()` as its installed `CellProgram`:

| Slot | Constant | Caveat | What it guarantees |
|:---:|---|---|---|
| `0` | `LEAD_SLOT` | `WriteOnce` | the appointed coordinator is pinned at open, then frozen |
| `1` | `BUDGET_SLOT` | `WriteOnce` | the swarm mandate cannot be widened mid-run |
| `2` | `SPENT_A_SLOT` | `Monotonic` | worker-A's spend only accumulates (no rollback to forge head-room) |
| `3` | `SPENT_B_SLOT` | `Monotonic` | worker-B's spend only accumulates |
| `4` | `EPOCH_SLOT` | `StrictMonotonic` | every step strictly advances the dispatch counter (no replay) |
| budget | `AffineLe` | `spent_a + spent_b - budget <= 0` | the agents COLLECTIVELY never spend past the mandate |

The Rust mirror of `metatheory/Dregg2/Apps/AgentOrchestrationBudget.lean` (the affine budget tooth,
the immutable mandate, the strict-monotone epoch) + `AgentOrchestration.lean` (the attenuated,
non-amplifying delegation — `worker_authority_subset_orchestrator`).

## Axis 3 — the service cell (`invoke()`, `src/service.rs`)

| method | semantics | auth | desugars to |
|---|---|---|---|
| `open_board(lead, budget)` | Replayable | `Signature` | `open_board_effects` (pin LEAD+BUDGET, meters 0, EPOCH 0→1) |
| `worker_step(...)` | Replayable | `Signature` | `worker_step_effects` (meter += cost, EPOCH +1, record tool/cost/sub-task) |
| `delegate_mandate(worker_cell)` | Replayable | `Signature` | `Effect::GrantCapability` (the worker tier, narrowed — `derive_no_amplify`) |
| `view()` | **Serviced** | `None` | — (the named OFE seam: a read, not a turn) |

```rust
use starbridge_agent_orchestration::service::BoardService;
use starbridge_agent_orchestration::{Tool, WorkerSlot};
use dregg_app_framework::InvokeAuthority;

let svc = BoardService::new(board_cell);
let turn = svc.worker_step(&cclerk, WorkerSlot::A, Tool::Search, 300, 300, 2, "index", InvokeAuthority::Signature)?;
executor.submit_turn(&turn)?; // the executor re-enforces AffineLe(spent_a + spent_b <= budget)
```

The cap-gate bites twice (front door AND executor); an over-budget `worker_step` is an executor
refusal on the `AffineLe` gate; `view` refuses to desugar (it names the serviced seam honestly).

## Axis 5 — the reactor (`src/reactor.rs`)

`CoordinatorReactor` watches the board for a committed `open_board` and reacts by auto-dispatching the
first `worker_step` (sized against the conserved budget). The on-chain coordinator agent-loop made
first-class: perceive the posted mandate off the observed receipt, plan the step, act by emitting its
own verified turn — re-enforced by the SAME `coordinator_program()`, so an autonomous coordinator can
never auto-dispatch past the mandate (an over-budget reaction is a real `AffineLe` refusal).

## What this crate exports

```rust
// Axis 1 — verified core
orchestration_factory_descriptor() -> FactoryDescriptor
coordinator_program()              -> CellProgram
build_open_board_action / build_worker_step_action      // signed Action builders
open_board_effects / worker_step_effects                // the shared effect bodies (AX3/AX5 reuse)
register(ctx: &StarbridgeAppContext) -> [u8; 32]        // factory + inspector + deos surface

// Axis 2 — deos surface
deos::orchestration_app(cclerk, executor) -> DeosApp
register_deos(ctx) / deos::fire_worker_step

// Axis 3 — service cell
service::BoardService                                    // .open_board / .worker_step / .delegate_mandate / .view
service::interface_descriptor() / service::register_interface(...)

// Axis 4 — deos-view card
card::board_card_value() -> serde_json::Value
card::board_card_json()  -> String

// Axis 5 — reactor
reactor::CoordinatorReactor

// Durable + auditable + MCP
OrchestrationEngine / OrchestrationLog / audit_run / recover / resume_plan
mcp::step_from_mcp_call / mcp::tool_for_mcp_name
```

## Tests

```sh
cargo test -p starbridge-agent-orchestration --release   # the embedded executor is slow in debug
```

| Test | Surface | What it pins |
|---|---|---|
| `src/lib.rs::tests` | the mandate lattice + program + builders | `granted ⊑ held`, attenuate-never-widens, the budget policy clauses |
| `src/service.rs::tests` | the `invoke()` builder | typed interface shape + front-door refusals |
| `src/card.rs::tests` | the view-tree | the card is a well-formed `deos.ui.*` tree whose buttons carry the service methods |
| `src/reactor.rs::tests` | the `Reactor` front door | an `open_board` drives an auto-dispatch; an over-budget reaction is an executor refusal; the cap-gate bites |
| `tests/service.rs` | **the real executor** | the lifecycle through `invoke()`: authorized commit, front-door cap-gate, executor re-enforcement, serviced seam |
| `tests/deos_surface.rs` | the axum surface | per-viewer projection, the gated `worker_step`, the durable posture, the cap teeth |
| `tests/orchestration_teeth.rs` | **the real executor** | the budget / epoch / mandate teeth bite end-to-end |
| `tests/mcp_binding.rs` | the MCP binding | a tool call runs as a verified step; an out-of-mandate call is refused |
| `tests/userspace_verify.rs` | `dregg-userspace-verify::analyze` | the plan is pre-flighted (conservation + non-amplification) before submission |

## See also

- `../swarm-orchestration/` — the in-memory twin (the SAME slots/program; AX3/AX4/AX5 exemplar).
- `../bounty-board/` — the reference 4-axis template.
- `../../docs/deos/DEOS-APPS.md` — the deos app model.
- `python/` — the Hermes guardrail differential (the tool-call seam, mirrored in Python).
