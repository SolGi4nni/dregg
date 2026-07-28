# starbridge-compute-exchange

**A compute marketplace — one verified cell that bounds a bid, pays a provider, and records the
split conservingly.** A requester needs work done; a provider has spare compute. They transact a
job neither trusts the other over, with **no escrow agent and no off-chain coordinator**. The
job *is* a factory-born cell whose installed `CellProgram` is the rules, re-checked by the
verified executor on every turn.

```
POSTED ──bid──▶ BID ──settle──▶ SETTLED
```

- **post**   — the requester opens a job: writes the promised `BUDGET`, `REQUESTER_HASH`, and a
  sealed `SPEC_HASH` (the job description). Nothing moves here.
- **bid**    — a provider bids `price ≤ BUDGET`, binds `PROVIDER_HASH`.
- **settle** — the deal closes: the accepted price is **paid** to the provider by a real
  conserving `Effect::Transfer`, in the same turn as the `STATE = SETTLED` advance.

## ⚑ A settlement moves value, and the budget is a promise

Until 2026-07-28 every settle builder here was `SetField` + `EmitEvent` and carried **no
`Effect::Transfer` at all**. The card rendered a green `SETTLED` pill and a live `paid ·`
amount over a payment that never happened. The four caveats below were all true and all about
the **record**: an `AffineEq` over `PAID + REFUNDED − BUDGET` relates three field slots, and
three numbers agreeing is not money moving.

`build_settle_actions` now emits the payment leg and the settle leg as **roots of one turn**, so
a requester who cannot cover the accepted bid takes the `SETTLED` stamp down with the transfer.

The budget is **not** escrowed, and the reason is the job cell's own program. Measured three
ways on this crate's factory-born cell, all refused: a cross-cell `SetField` needs the
destination's `set_state` to be `None`; a `Transfer` whose `from` is not the action target needs
the source's `send` to be `None`; and a funding action that credits the job without advancing
`STATE` is refused by `StrictMonotonic` (`field[9] did not strictly increase`), because the
executor evaluates a touched cell's program per action over every cell an effect touches,
including a transfer *destination*. Those have no common solution, so **a self-escrowing job
cell is not expressible.** Between `post` and `settle` nothing stops the requester spending the
money: a provider is protected against a settlement that lies, not against a requester who goes
broke. And `REFUNDED` is the part of the budget **never drawn** — it never left the requester,
so no refund transfer exists or could exist.

## Four guarantees, one cell program

Each guarantee is a slot caveat the verified executor enforces:

| Guarantee   | What it bounds                                | How this cell enforces it | Scope |
|-------------|-----------------------------------------------|---------------------------|-------|
| **BUDGET**  | a bid never exceeds the promised budget       | `FieldLteField { BID ≤ BUDGET }` — the accepted price is a bounded draw (the AffineLe budget gate); a provider cannot bid past the job's budget | every turn |
| **ACCEPTED**| the accepted price, bound exactly once        | `WriteOnce(BID)` — the requester accepts a price once; no silent renegotiation after acceptance | every turn |
| **FLASHWELL**| the settlement RECORD neither mints nor burns | no-mint `AffineLe { PAID + REFUNDED ≤ BUDGET }` (every turn) **and** no-burn `AffineEq { PAID + REFUNDED = BUDGET }` (settle) — over three field slots. The VALUE is moved by the settle's `Effect::Transfer`, which the kernel conserves per asset | see note |
| **LIFECYCLE**| one-way state machine                         | `StrictMonotonic(STATE)` — `POSTED→BID→SETTLED`; no regress, no replay, no double-settle | every turn |

> **The conservation invariant, honestly split.** The executor installs the descriptor's flat
> `state_constraints` and re-checks them *unconditionally* on every turn. The **no-mint** half
> (`PAID + REFUNDED ≤ BUDGET`) is universally true — `0 ≤ budget` before settle, equality at
> settle — so it is an executor-enforced invariant: **no party can ever extract more than was
> budgeted.** The exact **no-burn** equality (all the budget is accounted for) would be false at
> `bid` time, so it is scoped to the `settle` case of the canonical `child_program_vk` recipe
> (`job_cell_program`) and upheld by the settle fire, which reads live `BID` + `BUDGET` and pays
> the provider in full (`PAID := BID`, `REFUNDED := BUDGET − BID`). A value-minting settle is
> refused by the `AffineLe`; a value-burning settle is refused by the `AffineEq`.
>
> ⚠ **And read what it constrains.** Both halves relate `PAID`, `REFUNDED` and `BUDGET` — three
> *field slots*. Nothing in the constraint language relates a `Transfer` destination or amount to
> a state slot, so the executor does not force `PAID` to equal what actually moved, nor the payee
> to equal `PROVIDER_HASH`. The builders emit both legs from the same live values, which is a
> real check on a real committed value and explicitly **not** executor-enforced. Closing it needs
> new `StateConstraint` atoms: Lean-authored work on the constraint language, named here rather
> than improvised in Rust. `tests/settlement_conservation.rs` pins the gap so it cannot be
> forgotten.

Built from dregg primitives only — `FactoryDescriptor`, `Effect::SetField` /
`Effect::EmitEvent` / `Effect::Transfer`, `Authorization::Signature` from
`AppCipherclerk::make_action`, and Lane-G `StateConstraint` slot caveats. No domain-specific
compute `Effect`, no `Authorization::Unchecked`, no `[0u8; 64]` placeholder signatures.

## The deos-native surface

The whole interaction is one composed `DeosApp` (`job_app`), shipping from `src/lib.rs`. The
rights ladder `Signature ⊂ Either ⊂ None` **is** the observer ⊂ provider ⊂ requester roster:

- `view_job` — cap-only, `Signature` (an observer / auditor reads the job state);
- `bid` — gated (cap∧state), `Either` — a `POSTED` precondition; the fire submits the full bid
  turn, the executor re-enforcing the BUDGET gate;
- `settle` — gated (cap∧state), `None`/root — a `BID` precondition; the fire reads live
  `BID` + `BUDGET`, **transfers the accepted bid to the provider** and records the split, the
  executor re-enforcing FLASHWELL conservation on the record and `InsufficientBalance` on the
  payment.

The job cell is published into the web-of-cells as a `dregg://` sturdyref (a provider or
auditor on another federation reacquires the job across the membrane), and is discoverable
under `compute` / `marketplace`.

**The seam is closed.** The deos fire is two-tempo: a cap∧state precondition gate decides the
button in-band (nothing submitted on a miss — anti-ghost), then the full multi-effect turn is
submitted and the executor re-enforces the installed program. So an over-budget bid
(`FieldLteField`), a value-conjuring settle (`AffineEq`/`AffineLe`), and a non-advancing state
(`StrictMonotonic`, strict) are all **real executor refusals in the fire path** —
`tests/deos_seam.rs` proves each, with both polarities (the honest turn commits; the hostile
turn is refused and commits nothing). `tests/factory_birth.rs` proves the same teeth bite on a
factory-born cell, and `tests/settlement_conservation.rs` asserts the BALANCES on both poles: a
settled job moves the accepted bid to the provider, and an unfundable one is refused with the
provider still holding nothing and `STATE` still reading `BID`.

## Run the tests

```
cargo test -p starbridge-compute-exchange
```
