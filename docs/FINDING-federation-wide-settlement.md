# FINDING: federation-wide lease settlement needs the lease-program discharge, not a plain operator Transfer

Established 2026-07-10 while trying to make the demo lease's rent settle on every
replica. Surfaced *because* the orchestrator was made loud (it had been silent).

## The mechanism

DreggNet's provider settles metered rent with
`bridge/src/node_client.rs::submit_transfer` — a plain `Transfer { from: lease,
to: provider }` submitted to `POST /api/turns/submit`. The node signs every
thin-path turn as its **own operator cell** (confused-deputy hardening) and
executes it. A `Transfer` moving value *from* a cell requires that cell's
authorization: the operator can authorize a transfer from the lease **only if the
operator owns the lease**.

So the loop settles iff the lease cell is operator-owned. It was — until the demo
seed was made federation-wide (lease owned by a key derived from `federation_id`
so every replica seeds the identical cell). Then:
- the lease's owner key is not the operator → the operator-signed Transfer from it
  is refused `invalid authorization: hybrid: Ed25519 (classical) signature half
  failed`;
- and this broke the *single-node* loop too, which had settled only because the
  lease was operator-owned.

## The tension (why it's not a quick fix)

For a settlement to REPLICATE across the federation, both the `from` (lease) and
`to` (provider) cells must be federation-wide (identical on every replica) AND the
turn must be authorizable. A plain operator-signed Transfer can only move value
from an **operator-owned** cell, which is **per-node**. Federation-wide lease +
operator Transfer are mutually exclusive.

## The correct design (CORRECTED 2026-07-10 by a scholar study — the first draft was wrong)

**Retraction:** the original draft claimed the exec-lease `pay`/`advance` discharge
"operates on the lease WITHOUT requiring the caller to own it." That is **not
supported by the executor.** `pay_rent` (`execution-lease/src/lib.rs:604`) emits
exactly ONE `Effect::Transfer { from: lease, .. }` under `method == symbol("pay")`
— byte-for-byte the same effect kind `submit_transfer` already sends. The executor
authorizes it against the **lease cell's `Send` permission**
(`turn/src/executor/authorize.rs:2230`, `apply.rs:499`), verifying an Ed25519
signature against the *lease's* key. The `lease_cell_program` is a **post-transition
constraint checker, not an authorizer** — `TransitionGuard::Always`, invariants
WriteOnce(RENT/PERIOD/PROVIDER) + Monotonic(STEP/LAPSED/PERIODS_PAID)
(`lib.rs:287`); it runs *in addition to*, never *in place of*, the `Send` check, and
`method == "pay"` is invisible to it. So a `method:"pay"` swap is authorization-
equivalent to the plain transfer.

The ACTUAL path to a federation-wide, replica-applicable settlement is three real
steps (none an API-vocabulary change — the thin `/api/turns/submit` already
expresses everything):

1. **Federation-wide lease** — derive the lease key from `federation_id` (mirror the
   provider derivation). ~1h, but breaks the operator-signed transfer, so it cannot
   land alone.
2. **Seed the lease `Send = AuthRequired::None`** AND **add a balance-bounding
   program invariant** so a permissionless transfer can move only ONE period's rent,
   on-schedule, tied to `PERIODS_PAID`. Without the bound, a `Send=None` lease is a
   **drain vuln** — any caller empties the whole balance in one turn (the invariants
   constrain no balance). `BoundDelta` is the natural fit but is currently
   `BoundDeltaNotWired` (`cell/src/program/eval.rs:1297`), so this is a new
   executor-enforced "metered outflow" constraint WITH Lean/kernel parity — the
   ~3-5 day risk center.
3. **Provider side** — `NodeApiSettlement::submit_and_read` calls a `submit_lease_pay`
   (same body shape, `method:"pay"`); reconcile DreggNet's `decompose_charges` period
   numbering with the lease obligation's on-schedule `period_index`. ~1-2 days.

Total ~1 week; step 2 is the crux (kernel-parity constraint work). Do NOT ship a
bare `method:"pay"` swap — it achieves nothing and, with `Send=None`, is a drain.

## Current state (chosen for tonight)

- **Lease: operator-owned (per-node).** Restores the proven settlement loop
  (operator signs the Transfer from its own lease). Node-local.
- **Provider (rent beneficiary): federation-wide** — a real Ed25519 key derived
  from `federation_id`, seeded identically on every replica, so the metered
  Transfer credits a cell they all hold. (A raw blake3 digest is not a valid
  Ed25519 point and is refused; the key must be a real point.)

Net: a node-1 settlement moves value from node-1's lease to the shared provider.
It applies on node-1; it does not replicate (the other replicas lack node-1's
lease). Full federation-wide settlement waits on the discharge-path integration
above.
