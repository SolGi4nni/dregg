# Rate-Limited Allowance — bounded, self-refilling pocket money a sovereign agent can hand a sub-agent

An autonomous agent living inside dregg needs to hand a *sub-agent* BOUNDED
money: a budget that may spend up to a fixed ceiling of value per period and
**refills each period**, but can never be drained beyond that rate. This is the
house version of a *rate-limited allowance* — pocket money that resets every week
but cannot be over-spent within the week. The danger is twofold and symmetric:

* an **over-limit drain** — a spend that, together with what was already spent
  this epoch, exceeds the ceiling; and
* a **forged headroom** — tampering the committed `spent_this_epoch` DOWN to fake
  remaining budget, or advancing the epoch EARLY to illegitimately refill before
  the period boundary is genuinely crossed.

A rate-limited allowance closes both. The terms (`beneficiary`, `asset`,
`limit_per_epoch`, `epoch_length`, `start`) are sealed into the cell's
commitment, and a `spend` step is **bounded by the committed spent-counter** and
**monotone in the epoch cursor** — it resets `spent_this_epoch` to `0` and
advances `current_epoch` ONLY when the presented block genuinely crosses into a
later epoch, requires `spent_this_epoch + amount <= limit_per_epoch`, and writes
the advanced counter into the committed ledger. A holder of the commitment can
compute, for any block, exactly which epoch is current and how much of its budget
remains — so an over-limit spend is detectable, a forged counter diverges from
the commitment, and an early reset diverges from the schedule.

This is Track 2 (capacity) of *safely live within dregg*, VK-freedom era. It is
**built, not memoed** — a new module `cell/src/allowance.rs` — and it is a
**weld**: the substrate it needs (an openable committed heap, the signed balance
ledger, the one-shot/cursor discipline, block height as the clock) already
exists; the module joins it into the rate-limited-allowance capacity and adds the
**forge detectors** that make the ceiling load-bearing.

---

## 1. What a rate-limited allowance is

An allowance cell carries `AllowanceTerms` — a per-epoch spending grant:

> `beneficiary` may spend up to `limit_per_epoch` of `asset` per `epoch_length`-block
> epoch, starting at block `start`.

and three committed cursors tracking progress: `current_epoch` (the epoch the
committed counter belongs to), `spent_this_epoch` (value spent within that
epoch), and `spent_total` (the cumulative spent across all epochs). Epoch `k`
spans `[start + k·epoch_length, start + (k+1)·epoch_length)`; the epoch of a block
`b >= start` is `(b - start) / epoch_length`. The lifecycle:

| op               | meaning                                                                          |
|------------------|----------------------------------------------------------------------------------|
| `open_allowance` | bind the terms digest; `current_epoch = 0`, `spent_this_epoch`/`spent_total` `0` |
| `spend`          | if the block crosses into a later epoch, refill (reset `spent_this_epoch`); require `spent + amount <= limit`; debit and advance the counter |
| `remaining_at`   | at block `b`, the value still spendable in `b`'s epoch (`limit - spent_baseline`) |

The genuine minimal slice is a single **fixed-ceiling, fixed-length-epoch**
allowance in one asset, refilling to the full ceiling each epoch (no rollover of
unspent budget). Carry-over budgets, variable ceilings, multi-asset baskets, and
a bounded total-lifetime cap are the named next slice, not stubs here.

---

## 2. The weld (what already existed, disconnected)

The module welds onto substrate already in the tree, the same vehicles
`cell/src/escrow_sealed.rs`, `cell/src/derived.rs`, and
`cell/src/obligation_standing.rs` use — and it gives the **macaroon-layer budget
caveat** a committed, forge-detectable home:

* **The macaroon budget caveat** (`token/src/dregg_caveats.rs`:
  `DreggGrant::Budget { id, class, limit, window }`) is the *authority-side*
  primitive — it carries a per-window limit and rejects an obvious spoof
  (`remaining > limit`) and exhaustion (`remaining < cost`). But its `remaining`
  is **caller-asserted and unbound**: nothing ties it to committed state, so a
  caller free to choose its own `remaining` is the trust gap. This module is the
  **state-side dual**: `spent_this_epoch` lives in the commitment, so the
  headroom is *computed from the commitment*, not trusted — a forged-down counter
  is REJECTED. (The caveat decides *who may spend at what rate*; the allowance
  cell *enforces the rate against committed state*. Together they are the full
  rate-limited capability.)

* **The committed heap** (`CellState::set_heap` / `compute_heap_root`,
  `cell/src/state.rs`) is an openable sorted-Poseidon2 `(collection, key) →
  FieldElement` map ALREADY folded into the canonical state commitment. We
  reserve a collection id (`ALLOWANCE_COLL`) for the allowance ledger — the terms
  digest, the `current_epoch` cursor, the `spent_this_epoch` counter, and the
  cumulative `spent_total` all live there, bound into the cell's commitment **for
  free**, no commitment-version bump. (Same heap-binding discipline as
  `OBLIGATION_COLL` / `ESCROW_COLL`.)

* **The signed `i64` balance ledger** is the value primitive: each spend moves
  `amount` — exactly the quantity `CellState::balance` carries — and records it in
  the committed counter and cumulative.

* **Block height / a monotone counter** is the **epoch clock**: the epoch index
  for a block `b >= start` is `(b - start) / epoch_length`, and a refill is
  admissible only when the presented block genuinely lands in a later epoch than
  the committed cursor.

* **The nullifier / one-shot discipline** (the escrow leg-`Consumed` tooth, the
  obligation per-period cursor) is the shape the epoch cursor takes: the budget
  of an epoch is "consumed" up to the ceiling, and only the genuine crossing of an
  epoch boundary refills it. An early reset finds the cursor still in the same
  epoch and is REFUSED.

`EFFECT_TRANSFER` (the facet bit `1 << 1`, already named in `facet.rs`) is the
existing effect mask a spend rides on; no new facet bit is introduced.

---

## 3. The soundness story — what binds the ceiling

The terms' digest, the `current_epoch` cursor, the `spent_this_epoch` counter,
and the cumulative `spent_total` are written into `ALLOWANCE_COLL`, hence into the
cell's commitment. Against a holder of the commitment + heap openings, the binding
enforces:

1. **The ceiling.** A spend requires `spent_this_epoch + amount <=
   limit_per_epoch` (after any genuine epoch refill). A spend that would push the
   epoch's running total over the ceiling → `ExceedsCeiling`.

2. **No forged-down counter.** The remaining budget is computed from the
   *committed* `spent_this_epoch`, not taken on trust. A claim of "within budget"
   whose committed counter does not reflect prior spends diverges from the
   commitment and is REJECTED — and the committed `spent_total` is a second,
   independent witness: a forged-down epoch counter contradicts the un-forged
   cumulative, so the forge is internally inconsistent and detectable. The same
   `check_spend` the honest path runs reads whatever is committed.

3. **No early epoch reset.** A refill (resetting `spent_this_epoch` to `0`) is
   admissible only when the presented block crosses into a strictly later epoch
   than the committed cursor. The epoch is **derived from `at_block`**, not
   asserted — so advancing the epoch early to refill is *structurally impossible*:
   only a later block yields a later epoch, and a spend still inside the current
   epoch hits the ceiling.

4. **No stale-epoch overspend.** A spend whose block lands in an epoch EARLIER
   than the committed cursor (a backdated spend trying to reuse a past epoch's
   closed headroom) → `StaleEpoch`.

The honest-accept path (`spend` accepting) and every forge-reject path run
through the SAME `AllowanceState::check_spend` verification core, so a stub in
either direction fails one polarity (non-vacuity by construction).

---

## 4. The API (the genuine slice)

```rust
let terms = AllowanceTerms::new(beneficiary, asset, /*limit_per_epoch*/ 100,
                                /*epoch_length*/ 1000, /*start*/ 10_000);
open_allowance(&mut cell, &terms)?;                       // seal the rate

// in epoch 0 (block in [10_000, 11_000)), spend 40:
let moved = spend(&mut cell, &terms,
    &Spend { amount: 40, at_block: 10_500 })?;            // == 40, spent_this_epoch → 40

// at the genuine boundary (block >= 11_000) the budget refills:
spend(&mut cell, &terms, &Spend { amount: 100, at_block: 11_200 })?; // epoch → 1, reset then 100

// read-only spendable headroom at any block:
let view = AllowanceState::read(&cell)?;
allowance::remaining_at(&view, &terms, 11_500);           // == 0 (epoch 1 exhausted)
```

### The forges are genuinely rejected

Every forge detector shares the `check_spend` core with the honest path, and is
proven RED-on-break by **mutation**: stubbing `check_spend` to always-accept turns
the over-limit / forged-down-counter / early-reset / stale-epoch tests (and the
honest-rollover test, which depends on the genuine reset) RED while the honest
within-budget spend stays GREEN. Reverting the stub restores 13 green.

| forge                                                  | rejection            |
|--------------------------------------------------------|----------------------|
| spend **over** the remaining epoch budget              | `ExceedsCeiling`     |
| **forge-down** `spent_this_epoch` to fake headroom     | rejected — counter is committed; cumulative contradicts |
| **early epoch reset** (refill before the boundary)     | `ExceedsCeiling` (refill is structurally impossible) |
| **backdated** spend into a closed earlier epoch        | `StaleEpoch`         |
| present the **wrong terms** (forged higher ceiling)    | `TermsMismatch`      |
| a **non-positive** spend (free cursor advance)         | `NonPositiveAmount`  |

The honest within-budget spend ACCEPTS and advances the counter; the honest epoch
rollover refills the budget at the genuine boundary; and the allowance state is
bound into the canonical commitment (spending re-seals it — a light client sees
the counter move), so a forge cannot be hidden.

Tests: `cargo test -p dregg-cell --lib allowance::` — 13 green.

---

## 5. Next slice: circuit binding

The checks in §3–4 are **executor-level** — genuine forge rejections a verifier
runs in the clear. The remaining slice is the **in-circuit witness**, so that a
light client verifying a *batch* sees the ceiling enforced by the EffectVM circuit
(part of the proven kernel transition) rather than re-running the check out of
band:

1. A `SpendAllowance` effect descriptor whose **gate binds** *"`spent_this_epoch +
   amount <= limit_per_epoch` ∧ the counter is advanced
   (`spent_this_epoch' == spent_this_epoch + amount` within an epoch) ∧ the epoch
   is reset to `0` ONLY when `epoch_of(at_block) > current_epoch`
   (`current_epoch' == epoch_of(at_block)`, with `spent_this_epoch'` rebased on a
   genuine crossing)"* into the commitment — the same shape as the value/note
   gates already in `circuit/descriptors/`. The gate must bind the ceiling
   inequality, the counter-advance, and the boundary-gated reset into the
   commitment, else the rung is FALSE (the standing circuit-soundness apex bar).
   This is the one-shot nullifier shape the noteSpend grow-gate already carries,
   specialized to the per-epoch ceiling cursor.

2. The committed cursors (`current_epoch`, `spent_this_epoch`, `spent_total`) and
   the terms digest as **heap-opening witnesses** (each opened against the
   allowance cell's `heap_root`, the cell's commitment proven in the ledger root).

3. A Lean rung: `verifyBatch accept ⟹ allowance never overspent its rate` —
   concretely, a batch containing one or more spends implies that, in every epoch
   touched, the sum of spends did not exceed `limit_per_epoch`, the epoch cursor
   advanced only across genuine boundaries, and no closed epoch's headroom was
   reused — joining the circuit-soundness story tracked in
   `docs/reference/lean-circuit.md`.

Until that lands, rate-limited allowances are sound under the executor checks and
the commitment binding; the circuit rung is the named follow-up, not a silent gap.
(Unlike the sibling standing-obligation and membrane capacities, there is no
`invariant_matches_lean_rung` wired into `allowance.rs` yet — so this circuit
binding is genuinely the next slice, not a mislabel. An app-level model does
exist, though: `metatheory/Dregg2/Apps/Allowance.lean` promotes the falsification
probe `Dregg2.Verify.AllowanceFactoryProbe` into a live factory-instantiable
allowance cell.)
