# hosted-durable

**The conserving settlement + metering rail a hosted lease pays through — `LeaseCharge` →
one conserving `Effect::Transfer` → `SettleReceipt`, exactly-once and Σδ=0.**

This crate carries the half of the operated layer's durable-execution stack breadstuffs owns
natively: the value rail. A funded lease accrues per-period charges; each is settled as one
conserving transfer lessee → provider by a pluggable `Settlement` backend. The invariant the
fold upholds (and the tests prove): for any lease, `Σ settled(period) == Σ metered(period) ≤
budget`, and **every transfer conserves** (per-asset Σδ = 0 — the dregg value model).

## The core API

| item | where | what it is |
|---|---|---|
| `Settlement` (trait) | `src/settle.rs` | the single seam the biller drives: `settle` (idempotent on `(lease_id, period)`), `settled_total`, `funded_balance` (fail-closed `0`), `settled_turn_hash` |
| `LeaseCharge` | `src/settle.rs` | one period's charge — payer/beneficiary/asset/`(lease_id, period)`/amount |
| `SettleReceipt` | `src/settle.rs` | the receipt of one conserving move, with `replayed` making exactly-once observable |
| `PayableSettlement` | `src/payable.rs` | the production rail — each charge as one conserving `Effect::Transfer` turn over an injected `PaySubmitter` |
| `DurableSettlement` | `src/durable_settlement.rs` | restart-surviving: validate → write-ahead reserve → submit → confirm, over a durable settle ledger |
| `TestConservingLedger` | `src/settle.rs` | the explicit in-process double (NOT a production path) — its move still runs through the proven `apply_conserving_transfer` primitive |
| `Account` / `OverBudget` | `src/meter.rs` | a funded, refuse-over-budget meter account (atomic charge, never negative) + a process-global observability tally |
| `apply_conserving_transfer` | `src/conserve.rs` | the paired-delta conserving-move primitive, decided by the substrate's proven `CellState` signed-balance discipline (`recTransfer_balanceSum_conserve`) |
| `MeterCharge` / `read_meter_outbox` / `settle_meter_outbox` | `src/lib.rs`, `src/pg_outbox.rs`, `src/settle.rs` | the pg transactional-outbox meter (feature `pg`): per-period charge rows settled exactly-once end-to-end |

## How it fits the economy

`agent-platform::bill_period` builds a `LeaseCharge` from the rent `hosted-lease::check_bill`
returns, calls `Settlement::settle` (the one cross-cell payment), then `discharge`s the lease
(the in-cell meter+reserve draw). Settlement COMPLEMENTS the meter — `discharge` moves no value
cross-cell, `settle` is the single conserving payment; each bill draws and settles the same
`rent`, so no double-pay (settle is exactly-once by key, discharge is one-shot by cursor) and
no unpaid draw (`check_bill`'s `InsufficientBudget` backstop refuses over-reserve before settle).

## Honest limits

`TestConservingLedger` never leaves the process and yields no on-chain turn (`settled_turn_hash`
is `None`) — it is for offline tests, not a production default. The upstream durable-execution
*workflow* (duroxide orchestration over the operated compute tier + Postgres) is a named
follow-up, NOT imported here; the settlement rail stands complete without it.

## Tests

```sh
cargo test -p hosted-durable
```
