# starbridge-execution-lease

**Durable execution as a payable resource** — the "first primary resource" of the
agent service economy, modeled on dregg-native primitives. A fly.io-lite /
cloudflare-lite provider that **leases durable container execution to agents**,
metered and paid through the dregg value layer, with **no new kernel effect**.

## What it is

- A **provider** offers durable-execution slots from a factory
  (`lease_factory_descriptor`). A leased slot is a **lease cell**.
- A **lease** is a cap-bounded cell whose committed **heap** holds the agent's
  **durable execution image** (`EXEC_COLL`: a checkpoint step + a state digest +
  arbitrary working-memory keys). Because the heap is folded into the cell's state
  commitment, the durable state **survives**, is **passable** (a cell + its heap is
  a portable image), and is **witnessed** (a light client sees the checkpoint
  cursor move). This is what "durable execution" concretely IS here.
- The **meter** is a `StandingObligation` (`cell/src/obligation_standing.rs`): the
  lease OWES `rent_per_period` to the provider every `period` blocks. Each period
  is discharged once, on-schedule, for the exact rent — the recurring
  forge-detectors (no early / double / over / under discharge, no silent skip)
  bite.
- The **payment** is a `Payable` `pay` (`app-framework/src/payable.rs`) desugaring
  to ONE conserving kernel `Effect::Transfer` (lease → provider): per-asset Σδ=0
  holds across the lease.
- The **delivery** is a checkpoint advance: the durable cursor (`STEP_SLOT` +
  `STATE_DIGEST_SLOT`, mirrored into the heap) moves forward; the executor
  re-enforces `Monotonic(STEP_SLOT)`, so a rewind / forge of the durable cursor is
  a REAL refusal.
- The **lapse** is non-payment: when the schedule audit finds an undischarged
  period, the lease LAPSES (`LAPSED_SLOT`) and further delivery is refused (the
  provider reclaims the slot).

## The four axes

| axis | where |
|------|-------|
| verified core (FactoryDescriptor + CellProgram) | `src/lib.rs` |
| service cell (`invoke()` front door) | `src/service.rs` — `open` / `pay` / `advance` / `status` |
| deos-view card | `src/card.rs` |
| deos surface (composed `DeosApp`) | `src/lib.rs` — `lease_app` / `register_deos` |

## Prototype

`tests/durable_execution_lease.rs` walks the full flow: **lease → meter → pay per
period → durable state advances → lapse on non-payment**, asserting Σ CREDIT = 0
across the whole lease (leasing durable execution moves real value but never
creates or destroys it), plus the deos gated-`advance` fire (live vs lapsed).

```
cargo test -p starbridge-execution-lease
```

## Honest gaps

This is a faithful **model** of a durable-execution provider on the dregg value
layer — **not a real container runtime**. "Durable execution" here is the committed
umem cell-heap checkpoint image (a step cursor + a state digest + working memory),
advanced by the provider; it does not run agent code. The PAYMENT (a conserving
`Transfer`) and the durable-cursor forward-only tooth (`Monotonic(STEP_SLOT)`) are
REAL verified turns the executor enforces. The METER advance (the obligation
discharge) and the heap-checkpoint mirror are executor-side ledger steps — the same
named in-circuit seam `StandingObligation` describes (a `DischargeObligation`
effect binding "due ∧ not-discharged ⟹ discharged ∧ cursor advanced" into the
EffectVM so a light client, not just a re-executing validator, witnesses the
meter).

## How it feeds the fly.io-lite vision

The economic and durability shape is real and conserving today: a provider leases
metered, paid, lapsing durable slots, and the durable state is a witnessed,
passable cell-heap image. The production lane is welding a real WASM/OCI execution
engine to that checkpoint image (the agent's code runs against the durable heap;
each checkpoint snapshots the live image into `EXEC_COLL`), plus closing the named
`DischargeObligation` circuit seam so the meter is light-client-witnessed.
