# Standing Obligation — a schedule-enforced recurring debt a sovereign agent can carry

An autonomous agent living inside dregg needs to carry *standing duties*: rent, a
subscription, a periodic payment, a recurring tithe. Unlike a one-shot bonded
obligation (the deadline-and-slash `cell/src/blueprint.rs::ObligationTerms`), a
**standing obligation** is *recurring* — it owes `amount` at block `start`, again
at `start + period`, again at `start + 2·period`, and so on (forever, or until a
bounded `count`). The danger is twofold and symmetric:

* a **silent SKIP** — the obligor (or a malicious bookkeeper) claims "all paid
  up" while a due period went undischarged; and
* a **forged DISCHARGE** — claiming a period was paid *early* (before it came
  due), paid *twice* (double-discharge), or paid *more/less* than committed.

A standing obligation closes both. The schedule (`obligor`, `beneficiary`,
`asset`, `amount`, `period`, `start`, `count`) is sealed into the cell's
commitment, and a `discharge` step is **one-shot per period** and **monotone in
the cursor** — it advances a committed `next_due` cursor by exactly one period,
runs only once the schedule clock has reached the current due block, and writes
the discharged amount into the committed ledger. A holder of the commitment can
compute, for any block height, exactly how many periods MUST have been discharged
— so a skip is detectable and a forge diverges from the commitment.

This is Track 2 (capacity) of *safely live within dregg*, VK-freedom era. It is
**built, not memoed** — a new module `cell/src/obligation_standing.rs` — and it
is a **weld**: the substrate it needs (an openable committed heap, the signed
balance ledger, the one-shot nullifier discipline, block height as the clock)
already exists; the module joins it into the standing-obligation capacity and
adds the **forge detectors** that make on-schedule discharge load-bearing.

---

## 1. What a standing obligation is

An obligation cell carries `ObligationTerms` — a recurring debt declaration:

> `obligor` owes `amount` of `asset` to `beneficiary` every `period` blocks,
> starting at block `start`, for `count` periods (`0` = unbounded).

and three committed cursors tracking progress: `next_due` (the block at which the
next undischarged period falls due), `discharged_count`, and `discharged_total`.
Period `k` (0-indexed) falls due at `start + k·period`. The lifecycle:

| op                | meaning                                                                |
|-------------------|------------------------------------------------------------------------|
| `open_obligation` | bind the terms digest; `next_due = start`, count/total `0`             |
| `discharge`       | the current period is due ∧ amount conforms ⟹ pay it, advance the cursor by one period (one-shot from each period) |
| `audit`           | at clock `c`, the committed `discharged_count` must be ≥ the periods the schedule says are due by `c` |

The genuine minimal slice is a single **fixed-amount, fixed-period** obligation
with an optional bounded count. Variable amounts, grace windows, partial
discharges, and multi-beneficiary splits are the named next slice, not stubs
here.

---

## 2. The weld (what already existed, disconnected)

The module welds onto substrate already in the tree, the same vehicles
`cell/src/escrow_sealed.rs` and `cell/src/derived.rs` use:

* **The committed heap** (`CellState::set_heap` / `compute_heap_root`,
  `cell/src/state.rs`) is an openable sorted-Poseidon2 `(collection, key) →
  FieldElement` map ALREADY folded into the canonical state commitment. We
  reserve a collection id (`OBLIGATION_COLL`) for the obligation ledger — the
  schedule digest, the `next_due` cursor, the discharged count, and the
  cumulative total all live there, bound into the cell's commitment **for free**,
  no commitment-version bump. (Same heap-binding discipline as `ESCROW_COLL`.)

* **The signed `i64` balance ledger** is the value primitive: each discharge
  moves `amount` — exactly the quantity `CellState::balance` carries — and
  records it in the committed cumulative.

* **Block height / a monotone counter** is the **schedule clock**: period `k`'s
  due block is `start + k·period`, and a discharge is admissible only when the
  presented clock has reached the current due block.

* **The nullifier / one-shot discipline** (the escrow leg-`Consumed` tooth) is
  the shape the per-period cursor takes: a discharge of period `k` is admissible
  only when `next_due == start + k·period`, and it advances the cursor to
  `start + (k+1)·period`. A second discharge of period `k` finds the cursor
  already past it and is REFUSED — a spent period is a spent nullifier.

`EFFECT_OBLIGATION_OPS` (the facet bit `1 << 14`, already named in
`facet.rs::effect_names`) is the existing effect mask this capacity rides on; no
new facet bit is introduced.

---

## 3. The soundness story — what binds the schedule

The terms' digest, the `next_due` cursor, the discharged count, and the
cumulative total are written into `OBLIGATION_COLL`, hence into the cell's
commitment. Against a holder of the commitment + heap openings, the binding
enforces:

1. **No early/forged discharge.** A discharge of the current period requires the
   presented schedule clock to have reached that period's due block
   (`start + k·period`). A discharge before due → `NotYetDue`.

2. **No double-discharge (one-shot per period).** The `next_due` cursor advances
   by exactly one period on each discharge; the period being paid is **derived
   from the committed cursor**, not taken on trust from the step. A second
   discharge of an already-paid period finds the cursor advanced →
   `WrongPeriod`. A skip-ahead (paying a future period while the current one is
   undischarged) hits the same check.

3. **No over/under-discharge.** The discharged amount must equal the schedule's
   committed `amount`; any divergence → `AmountMismatch`.

4. **No silent skip / staleness.** `ObligationState::audit` computes, from the
   schedule and a presented clock, how many periods MUST be discharged by now
   (`ObligationTerms::periods_due_by`), and rejects a committed `discharged_count`
   below it → `BehindSchedule`. A cell claiming "all met" whose committed cursor
   lags the schedule is REJECTED by **the same `audit`** an on-schedule cell
   passes.

The honest-accept path (`discharge` accepting) and every forge-reject path run
through the SAME `ObligationState::check_discharge` / `audit` verification core,
so a stub in either direction fails one polarity (non-vacuity by construction).

This executor invariant is **PROVEN, not just smoke-tested**: the on-schedule /
never-skipped discipline is the executor image of the kernel-clean Lean rung
`metatheory/Dregg2/Deos/StandingObligation.lean` (grounded by reuse of the
committed-heap root + the `StrictMonotonic` cursor discipline), and
`obligation_standing.rs::invariant_matches_lean_rung` mirrors that rung's
witnesses on the Rust side.

---

## 4. The API (the genuine slice)

```rust
let terms = ObligationTerms::new(obligor, beneficiary, asset, /*amount*/ 50,
                                 /*period*/ 100, /*start*/ 1000, /*count*/ 0);
open_obligation(&mut cell, &terms)?;                       // seal the schedule

// at block >= 1000, discharge period 0:
let moved = discharge(&mut cell, &terms,
    &Discharge { period_index: 0, amount: 50, clock: 1000 })?; // == 50, cursor → 1100

// auditing the cell against the schedule at any clock:
ObligationState::read(&cell)?.audit(&terms, 1250)?;        // requires >= 3 periods by 1250
```

### The forges are genuinely rejected

Every forge detector shares the core verifier with the honest path, and is
proven RED-on-break by mutation: stubbing `check_discharge` to always-accept
turns the early / skip-ahead / double-discharge / over-under / wrong-terms /
bounded-complete tests RED while the honest path stays GREEN; stubbing `audit`
turns the silent-skip test RED alone.

| forge                                        | rejection            |
|----------------------------------------------|----------------------|
| discharge **before** the due block           | `NotYetDue`          |
| discharge a period **twice** (replay)        | `WrongPeriod`        |
| **skip ahead** to a future period            | `WrongPeriod`        |
| discharge **more or less** than owed         | `AmountMismatch`     |
| claim "all met" while **behind schedule**    | `BehindSchedule`     |
| present the **wrong terms**                  | `TermsMismatch`      |
| discharge past a **bounded count**           | `Completed`          |

The honest on-schedule discharge ACCEPTS and advances the cursor, and the
obligation state is bound into the canonical commitment (discharging re-seals it
— a light client sees the cursor move), so a forge cannot be hidden.

Tests: `cargo test -p dregg-cell --lib obligation_standing::` — 14 green.

---

## 5. The circuit binding (BUILT — VK-epoch flip is the last seam)

The checks in §3–4 are **executor-level** — genuine forge rejections a verifier
runs in the clear. The **in-circuit witness** — so that a light client verifying
a *batch* sees on-schedule discharge enforced by the EffectVM circuit (part of
the proven kernel transition) rather than re-running the check out of band — is
now **built**, not a pending slice:

1. The `DischargeObligation` effect descriptor is emitted. The tag-18 emit
   keystone `metatheory/Dregg2/Deos/DischargeSatDescriptor.lean`
   (`dischargeSatVmDescriptor2R24 cur tot due`) carries the genuine
   `EffectVmDescriptor2` at the deployed v12 / R=24 rotated geometry, plus the
   **refinement rung**: a satisfying trace with the capacity selector on FORCES
   the discharge discipline (due `clock >= start + k·period` ∧ not-yet-discharged
   `next_due == start + k·period` ⟹ discharged ∧ cursor advanced by one period,
   `next_due' == next_due + period`, `count' == count + 1`). The in-AIR gate
   polynomials — the cursor-advance, the total-advance, and the due-ness range
   gadget with constraint-level teeth — live in
   `circuit/src/effect_vm/discharge_weld.rs`. This is the one-shot nullifier
   shape the noteSpend grow-gate already carries, specialized to the per-period
   cursor.

2. The committed cursors (`next_due`, `discharged_count`, `discharged_total`) and
   the terms digest are bound as **heap-opening witnesses** (each opened against
   the obligation cell's `heap_root`, the cell's commitment proven in the ledger
   root).

3. The Lean rung — `verifyBatch accept ⟹ obligation honored on schedule`,
   concretely: a batch containing a discharge implies the period was genuinely
   due and undischarged before and is discharged with the cursor advanced after,
   with no period discharged twice across the batch — joins the circuit-soundness
   story tracked in `docs/reference/lean-circuit.md`.

The **one honest remaining seam** is the deliberately-gated **VK epoch flip**:
committing the wide-welded VK that exposes the tag-18/19 discharge PIs and
flipping the deployed default on. The descriptor and weld themselves are built;
until the flip, standing obligations are witnessed by the executor rung + the
commitment binding, with the circuit descriptor staged behind the VK gate.
