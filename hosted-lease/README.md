# hosted-lease

**The hosting lease, dregg-native — a durable-execution image + a `Monotonic` checkpoint
cursor + a rent meter, built on the proven `starbridge_execution_lease` capacity rather than
a local struct.**

`HostedLease` is the seam a hosted runtime binds to: it reads the lease's committed durable
image (`EXEC_COLL`), runs the agent's code, and `checkpoint`s to advance the cursor with the
new state digest and working memory — so the durable state survives, is passable (a cell + its
heap is a portable image), and is witnessed (a light client sees the cursor move). A rewind or
forge of the durable image is a real executor refusal, not a convention.

## The core API (`src/lib.rs`)

| method | what it does |
|---|---|
| `open` | open an obligation-metered lease initialised to a genesis digest (seals the rent obligation + `WriteOnce` economics + genesis checkpoint) |
| `open_prepaid` | open a **FUSED prepaid** lease — the durable image genesis PLUS the `prepaid_lease` meter+reserve, so each bill's reserve-draw and meter-advance are one atomic write |
| `check_bill` | read-only gate: the rent this period WILL draw, refusing off-schedule / replay / over-draw / exhausted-reserve (`InsufficientBudget`) BEFORE any value moves |
| `discharge` | the ONE atomic write that draws exactly the sealed rent from the reserve AND advances the meter cursor |
| `meter` | the OBLIGATION-path per-period discharge (returns the rent a separate settlement must move; no fused draw) |
| `checkpoint` | advance the durable image: move the cursor, re-bind the state digest, write `working` memory (keys ≥ `WORKING_BASE`); refuses on a lapsed lease |
| `lapse_if_behind` | lapse a lease behind on rent (obligation-schedule audit, or the prepaid audit + the dry-reserve backstop), latching `LAPSED_SLOT` |
| `from_cell` / `from_cell_prepaid` | wrap an ALREADY-opened lease cell (e.g. opened by `starbridge_vat::lifecycle::open_vat_prepaid`) without re-opening the `WriteOnce` slots |

## The two metering modes (`Metering`)

- **`Obligation`** — a `StandingObligation` cursor metered per period, PAID by a separate
  settlement draw. Meter and pay are two enforced pieces coupled by app control flow.
- **`Prepaid(PrepaidLeaseTerms)`** — the FUSED `dregg_cell::prepaid_lease` capacity draws rent
  from a sealed reserve in the SAME write that advances the cursor, so **meter/pay drift is a
  type error, not a discipline**. This is the mode `agent-platform` rents on.

## How it fits the economy

`agent-platform::rent` opens a prepaid `HostedLease` on the tenant's lease cell; `bill_period`
drives `check_bill` → (settle via `hosted-durable`) → `discharge`; `grain-fork::Grain` funds
its mind's rent through an obligation `HostedLease`. The durable image is where a grain's
resumable session carrier and vat lifecycle are sealed (slots disjoint from the economics).

## Honest limits

The lease meters and audits value; it does not itself move cross-cell value — pair it with a
`hosted_durable::Settlement`. On a prepaid lease, `meter` is a `NotALease` refusal (metering
goes through the fused `discharge`), and vice-versa — the mode is not silently interchangeable.

## Tests

```sh
cargo test -p hosted-lease
```
