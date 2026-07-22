# DESIGN — partial turns and promises: the guarded-hole keystone

Status: DESIGN over a **largely-built** substrate. 2026-07-16.
Scope: the turn / effect / receipt model in `turn/src/` and the metatheory in
`metatheory/Dregg2/`. This doc describes what a guarded hole IS, catalogues the
pieces that already exist (with `file:line` anchors verified at HEAD), and marks
the genuinely-NEW work — the in-circuit witness for the fill — as the first slice.

A note on honesty up front: this is **not** a greenfield feature. The "weak"
guarded hole is a first-class, `#assert_axioms`-clean Lean object today, and the
promise/fill effect pair is in the deployed Rust `Effect` vocabulary today. The
design contribution here is (a) naming the semantics precisely, (b) stating the
anti-abuse properties as they are actually enforced (not as they read in a
header), and (c) isolating the one VK-affecting lift that remains.

---

## 1. What a guarded hole IS

A **guarded hole** is a typed promise: a slot in a turn's effect stream that
commits *now* but is filled by a *later* resolution turn, and only if a **guard**
predicate holds at fill time. Concretely it is two things bound together:

- a **promise** — an effect that is really committed into the ledger now (it lands
  in `effects_hash`, hence in the receipt; it is not an off-ledger IOU), and
- a **guard** — a predicate a future filler MUST discharge before the fill effect
  is admitted.

The guarded-hole study (`metatheory/docs/GUARDED-HOLES-METATHEORY.md`) split the
idea in two, and the split is load-bearing for this whole design:

- The **WEAK guarded hole** — a `Pred` guard on a late-filled *value* slot,
  discharged at fill time — is elegant, composes, and is *mostly already code*
  ("predicated pipelining"). It is BUILT (§2).
- The **STRONG guarded hole** — a hole in a *conservation or authority* position
  (an undetermined δ, a lazy SHAPE) — is a flaw in the IDEA, and is deliberately
  **inexpressible** in dregg. There is no non-zero-δ primitive; joint turns take
  the whole agreeing cone; authority must be in-circuit. Failure is by
  inexpressibility (safe), not by a silent hole (§6).

The one-line verdict that governs the design: **determination is EAGER, witness is
LAZY.** A contribution's SHAPE — which field it writes, whose authority it demands,
its exact δ — is fixed when the hole is created. Only its VALUE / discharging proof
arrives later. Every hole dregg admits is a lazy witness over an eager shape.

---

## 2. What EXISTS today (grounded)

### 2.1 The weak guarded hole is first-class in Lean — PROVED

`metatheory/Dregg2/Exec/GuardedHole.lean` builds the weak hole as a first-class
object, `#assert_axioms`-pinned:

- `structure GuardedHole` (`GuardedHole.lean:37`) with fields
  `field : FieldName`, `actor : CellId`, `target : CellId`,
  `guard : List PredCaveat` — the EAGER shape (which slot, whose write, under
  which predicate) is fixed at creation; only the value is lazy.
- `def fillGuarded (h) (s) (n : Int) : Option RecChainedState` (`GuardedHole.lean:48`)
  — the fill IS `predStateStepGuarded` (`PredAlgebra.lean:580`), the guarded `put`:
  it commits the underlying `stateStep` write **iff** every `PredCaveat` of
  `h.guard` admits the `(actor, old, n)` transition. Fail-closed on a violating
  value.
- **The keystone** `theorem holeFill_binds_in_circuit` (`GuardedHole.lean:59`): a
  successful fill binds BOTH legs into the committed post-state — its δ (the
  post-state is *exactly* the `stateStep` write, no hidden mutation) AND its guard
  (`predCaveatsAdmit h.guard … = true`). So a hole cannot be filled without
  committing its effect and the predicate it promised.
- **The negative tooth** `theorem holeFill_rejects_guard_violation`
  (`GuardedHole.lean:67`): a value violating the guard fills to `none`.
- Non-vacuity: `demoHole` (`GuardedHole.lean:77`) has a two-valued guard (admits
  `50`, rejects `55`), and `(fillGuarded demoHole demoState 55).isNone` is a
  passing `#guard` — the tooth FIRES, it is not a `P → P` tautology.

This is the abstract state-fill. The rest of §2 is its concrete, deployed
instantiation in the turn effect vocabulary.

### 2.2 The promise/fill effect pair is DEPLOYED — Promise / Notify / React

The `Effect` enum (`turn/src/action.rs:1060`, 34 live variants, reified and
exhaustiveness-checked against Lean in `metatheory/Dregg2/Substrate/VerbRegistry.lean`)
carries a first-class reactive triple:

- `Effect::Promise { cell, resolution_condition, wake: Box<Turn>, timeout_height }`
  (`action.rs:1440`) — a STANDING COMMITMENT: `cell` commits to run `wake` once
  `resolution_condition` holds. LinearityClass **Generative** (it creates a hole).
- `Effect::Notify { from, to, wake, resolution_condition, timeout_height }`
  (`action.rs:1454`) — the same hole-mint, deposited CROSS-CELL in the recipient's
  registry. Generative.
- `Effect::React { pending_id: Nullifier, condition: ProofCondition,
  resolution_proof: ConditionProof, wake: Box<Turn> }` (`action.rs:1471`) — the
  FILL: discharge the hole `pending_id` by presenting a proof of `condition`.
  LinearityClass **Terminal** (one-way consume of the hole, no inverse).

The kernel weld is `turn/src/reactive.rs` (the `ReactiveEffect` ADT +
`ReactiveCoordinator`, `reactive.rs:83`). Its design keystone — the reason this is
sound by construction — is stated at `reactive.rs:31`:

> **A promise-hole is a React-domain nullifier. To react is to spend the hole.** One-shot
> linearity uses the same abstract fresh-insert discipline as a note spend, but a dedicated
> `ReactiveNullifierSet` and domain-separated commitment keep it out of faithful FNSP note history.

`VerbRegistry.lean` ratifies this classification: `Promise`/`Notify` classify to
the `shieldUnshield` verb (shield direction / hole-mint), `React` to
`shieldUnshield` (unshield direction / hole-spend), with the `#guard`
`classify .React == classify .NoteSpend` (`VerbRegistry.lean:488`) — *a react is a
nullifier spend*, structurally.

### 2.3 The escrow-shaped conditional — ConditionalTurn

`turn/src/conditional.rs` is the promise-shaped primitive the reactive triple
builds ON. It predates the guarded-hole framing and answers a narrower question:
"execute this turn IFF a proof arrives before a deadline."

- `enum ProofCondition` (`conditional.rs:55`) — 4 guard classes: `HashPreimage`
  (HTLC preimage), `RemoteProof` (a STARK from a remote federation, root-anchored),
  `LocalProof` (a local STARK with pinned public inputs), `TurnExecuted` (a signed
  receipt for a named turn).
- `struct ConditionalTurn { turn, condition, timeout_height, submitted_at,
  deposit_amount }` (`conditional.rs:89`) — the deferred turn plus its escrow
  economics: a `deposit_amount` locked at submission, **refunded on resolution,
  burned on timeout** (`refund_conditional_deposit` / `burn_conditional_deposit`,
  `conditional.rs:558`/`:566`). This is exactly the escrow shape the task names.
- `fn resolve_condition(condition, proof, current_height, timeout_height,
  trusted_roots, max_root_age, used_proof_hashes, trusted_executor_keys)`
  (`conditional.rs:198`) — the fill gate. It checks timeout (`current_height >
  timeout_height ⇒ Expired`), the **proof nullifier** (`used_proof_hashes`, replay
  prevention), root freshness, AIR-name binding (fail-closed on an unregistered
  descriptor via `descriptor_by_name`), and constraint satisfaction.

`React` reuses `ProofCondition` and `resolve_condition` verbatim as its guard —
see `action.rs:1477` (`condition: ProofCondition`) and the executor path in §4.

### 2.4 The pending registry — cascade, timeout, broken-promise

`turn/src/pending.rs` holds the holes between commit and fill:

- `struct PendingEntry { turn, condition, dependents, submitted_at, timeout_height }`
  (`pending.rs:43`) — a promise-hole and the turns waiting on it.
- `enum ResolutionCondition` (`pending.rs:58`) — `AwaitReceipt { turn_hash,
  federation_id }` / `AwaitCondition(ProofCondition)` / `AwaitHeight(u64)`.
- `PendingTurnRegistry` (`pending.rs:165`) with `submit_pending_at`, `resolve`
  (removes the entry and cascades to dependents), `check_timeouts`. Broken promises
  propagate: `BrokenReason::DependencyBroken` (`pending.rs:92`) cascades a break
  down the dependent graph.

### 2.5 The promise-pipelining datastructure and its light-client lift — Lean

`metatheory/Dregg2/Exec/ConditionalTurn.lean` is the executable, proved model of a
*partial turn with holes*: a `ConditionalBatch` (nodes = turns, edges =
`EventualRef` dependencies), executed in Kahn topological order via
`execConditionalTurn`, all-or-nothing, with the run order proven to respect every
dependency edge. `metatheory/Dregg2/Exec/ConditionalTurnLift.lean` refines such a
batch node down into the DEPLOYED apex `Effect` vocabulary (`execFullTurnA` over
`liftNode` / `FullAction.toA`), so a value-only or authority-only batch turn is
light-client-verifiable **through the existing VK, with no new selector column**
(rungs A/B/C, `#assert_axioms`-clean; residual = the composite mixed-node +
inter-node topo fold, named NON-VK bookkeeping).

---

## 3. How a promise commits (it is a real effect, not a deferral off-ledger)

A `Promise`/`Notify` is an ordinary effect inside a turn's `Action::effects`
(`action.rs:85`). It goes through the normal apply path and is bound into the
receipt like any other effect:

- The executor's `apply_promise` (`turn/src/executor/apply.rs:1446`) gates
  `cell == actor` (a cell makes its OWN commitments — no cross-cell injection) and
  submits the hole into the reactive registry.
- `apply_notify` (`apply.rs:1480`) gates `from == actor` (no spoofed provenance)
  and `wake.agent == to` (the recipient only ever commits to turns IT would run).
- Because it is a committed effect, the promise lands in the turn's `effects_hash`,
  which is bound into `receipt_hash` (`turn/src/turn.rs:109`, `:466`). A light
  client folding the receipt therefore sees *that a promise was made*, its
  condition, and its timeout — the hole is on the record, not in a side channel.

This is the answer to the memory's original open question ("what does NOT exist: a
first-class EFFECT carrying the batch"): the hole IS a first-class effect now. The
`Generative` linearity class discloses on-chain that a resource (a hole) was
created without a paired consumer in the same turn — the fill comes later.

---

## 4. How the resolution turn fills the hole (one receipt binds three things)

The fill is `Effect::React`, applied by `apply_react`
(`turn/src/executor/apply.rs:1536`). In ONE turn, it binds the promise-id, the
guard-satisfaction, and the fill effect, in this order (fail-closed at each step):

1. **Well-formedness** — reject a null `pending_id` (`apply.rs:1547`), the same
   guard `NoteSpend` applies to its nullifier.
2. **Nullifier↔turn binding** — `wake.hash() == pending_id.0` (`apply.rs:1560`).
   The spent hole id IS the resolved turn's hash, so a react cannot spend one hole
   while resolving an unrelated `wake`.
3. **Guard discharge** — `resolve_condition(condition, resolution_proof, …)`
   (`apply.rs:1587`) must return `Resolved`. This enforces the timeout and the
   proof's validity. A wrong or expired proof spends nothing.
4. **The one-shot spend** — `pending_id` is consumed into the production
   `note_nullifiers` set with double-spend rejection, **journaled** (so it rolls
   back if the turn later fails). This is the SAME set that gates `NoteSpend`
   (`apply.rs:1236`, `:1376`). A second react — or a replay of the same
   `pending_id` — hits the identical gate and is rejected.
5. If a matching hole is live in the reactive registry, `resolve` it with a genuine
   receipt over the resolved turn (registry removal — a redundant second tooth; the
   nullifier gate is the load-bearing one).

The result: the fill's own effects land in the resolution turn's `effects_hash`,
and the hole-nullifier grows — both on the same receipt.

---

## 5. Anti-abuse properties (as actually enforced)

| property | enforced by | anchor |
|---|---|---|
| A hole cannot be filled without its guard | `resolve_condition` must return `Resolved` before the spend | `apply.rs:1587`; Lean `holeFill_rejects_guard_violation` `GuardedHole.lean:67` |
| A filled hole cannot be re-filled | `pending_id` spent into `note_nullifiers`; double-spend rejected; + registry removal | `apply.rs`; `reactive.rs:38` (two teeth) |
| A react cannot spend one hole while resolving another | `wake.hash() == pending_id` | `apply.rs:1560` |
| Proof replay across holes | `used_proof_hashes` nullifier in `resolve_condition` | `conditional.rs:212` |
| Stale / untrusted root | root-in-trusted-set + age ≤ `max_root_age` | `conditional.rs:301` |
| Prover cannot choose the constraint it is checked against | descriptor resolved from the CONDITION's `air_name` via `descriptor_by_name`, fail-closed on unknown | `conditional.rs:339` |
| Timeout griefing | `deposit_amount` burned on timeout; deposit ∝ blocks held | `conditional.rs:533`, `:566` |
| No cross-cell hole injection | `Promise`: `cell == actor`; `Notify`: `from == actor` ∧ `wake.agent == to` | `apply.rs:1457`, `:1492`, `:1502` |
| Fill mutates nothing hidden | Lean: post-state is EXACTLY the `stateStep` write | `holeFill_binds_in_circuit` `GuardedHole.lean:59` |

**Conservation across the promise+fill.** This is the subtle one and it is worth
stating precisely, because it is the reason the STRONG hole is forbidden. The
promise and the fill are TWO turns; dregg's conservation invariant
(`Σδ = 0` per asset, per turn — `execFullTurnA_conserves_exact` in the metatheory)
holds **within each turn**, not across the pair. This is sound only because the
hole reserves NO resource: the promise's δ is the hole-mint (evidence ↑, no value
moved), and the fill's δ is whatever the `wake` turn does — itself a conserving
turn. A hole that carried an undetermined *value* contribution (a δ filled later)
would break turn-local conservation, and that is exactly the strong hole dregg
refuses to express (§6). The weak hole moves conservation-neutral evidence
(nullifier growth); value only ever moves inside a fully-determined turn.

---

## 6. The strong hole is inexpressible — by design, not omission

A hole in a conservation or authority position — "I contribute an amount TBD",
"this turn is authorized by a proof filled later" — is a lazy SHAPE, and dregg has
no primitive for it:

- No non-zero-δ primitive: `execFullTurnA_conserves_exact` needs
  `ledgerDeltaAsset_eq_zero = 0`; there is no verb that moves an undetermined value.
- Joint turns take the WHOLE agreeing cone (`IsWideJointTurn.lift`); temporal
  partiality of a multi-party turn is deliberately forbidden.
- Authority must be in-circuit — a fill cannot retroactively supply the authority
  a turn already spent under.

So a "partial turn" that tries to defer a δ or an authority demand fails by
**inexpressibility** — the type does not exist — rather than by a silent hole that
a later fill could exploit. This is the safe failure mode, and it is the guardrail
`holeFill_binds_in_circuit` formalizes for the value/witness that IS deferrable.

---

## 7. Lean type sketch — real objects + the proposed extension

The real, deployed abstract fill (verbatim shape from `GuardedHole.lean`):

```lean
structure GuardedHole where
  field  : FieldName          -- the slot the fill writes (an EventualRef landing field)
  actor  : CellId             -- who fills
  target : CellId             -- the cell written
  guard  : List PredCaveat    -- the predicate promised UP FRONT (the eager shape)

def fillGuarded (h : GuardedHole) (s : RecChainedState) (n : Int) : Option RecChainedState :=
  predStateStepGuarded h.guard s h.field h.actor h.target n   -- guarded `put`; none if guard rejects

theorem holeFill_binds_in_circuit (h : GuardedHole) {s s' : RecChainedState} {n : Int}
    (hfill : fillGuarded h s n = some s') :
    stateStep s h.field h.actor h.target (.int n) = some s'      -- δ bound
    ∧ predCaveatsAdmit h.guard s.kernel h.field h.target n = true  -- guard bound
```

The deployed effect faces (verbatim shape from `turn/src/action.rs`, rendered as
Lean for the metatheory correspondence):

```lean
-- promise-hole (Generative): mint a hole in `cell`'s registry
| Promise (cell : CellId) (cond : ResolutionCondition) (wake : Turn) (timeout : Nat)
-- the fill (Terminal): spend the hole `pendingId` under a discharged proof
| React   (pendingId : Nullifier) (cond : ProofCondition)
          (proof : ConditionProof) (wake : Turn)   -- requires wake.hash = pendingId
```

**PROPOSED (the NEW theorem, not yet discharged for this exact ADT).** The Lean
`holeFill_binds_in_circuit` is about an abstract `stateStep`; the deployed `React`
binds via the dedicated `ReactiveNullifierSet` in the *executor*, not yet in the *circuit*.
The proposed keystone would state that a light client folding a batch bearing a
`React` sees the dedicated React replay commitment grow without changing the faithful note root:

```lean
-- PROPOSED — the React circuit-witness lift (VK-affecting; see §8)
theorem react_grows_dedicated_replay_state
    (b : FullForestA) (e : React …) (he : e ∈ effectsOf b) :
    reactiveNullifierRoot (execFullTurnA … b).after
      = reactiveNullifierInsert (reactiveNullifierRoot before) e.pendingId
    ∧ noteNullifierRoot (execFullTurnA … b).after = noteNullifierRoot before
    ∧ e.wake.hash = e.pendingId          -- the executor's binding, now in-circuit
```

This theorem does not exist yet. Its Rust-side enforcement does (§4); the lift is §8.

---

## 8. Honest relation to conditional.rs, and the first slice

`conditional.rs` already IS a promise primitive — a deferred turn, an escrow
deposit, a proof-gated fill with a nullifier against replay. The guarded-hole work
does not replace it; it **generalizes the fill into the effect vocabulary** so the
promise and the fill are ordinary receipted effects rather than a separate
`ConditionalTurn` submission path. `React` reuses `conditional.rs`'s
`ProofCondition` + `resolve_condition` unchanged as its guard. The two coexist:
`ConditionalTurn` is the whole-turn escrow envelope; `Promise`/`React` are the
per-effect holes inside a turn's forest.

**The one genuinely-open piece — the first slice.** `reactive.rs:48` names it
explicitly, and it is the only VK-affecting work here:

> Lean obligation named (NOT yet discharged for this exact ADT): the circuit
> witness for a `React` effect — that a light client verifying a batch bearing a
> `React` grows the dedicated React replay commitment and leaves the faithful note root unchanged.

Today the one-shot property is enforced **executor-side** (the `reactive_nullifiers`
insert in `apply_react`). A pure light client — one that folds receipts without
re-executing — does not yet witness the hole-spend in-circuit. The first slice:

1. Give `React` its own domain-separated replay-state descriptor rung,
   reading `pending_id` as the spent React id and asserting the
   `wake.hash == pending_id` binding in-circuit.
2. Route it through `convert_turn_effects_to_vm` so the committed React count is
   non-zero and the per-turn fold binds the nullifier growth (the same shape the
   Custom-effect door uses, `action.rs:1547`).
3. Discharge `react_grows_nullifier_like_noteSpend` (§7) against the real
   `FullForestA` fold, `#assert_axioms`-clean.

This is VK-affecting and therefore **ember-gated** — it lands on the same footing
as the ShieldedTransfer and SetProgram circuit residuals already tracked in
HORIZONLOG.

---

## 9. Hard parts and open questions

- **Conservation across a two-turn promise.** Handled today ONLY because the hole
  reserves no resource (§5). If a future feature ever wants a value-bearing hole,
  it must re-impose turn-local conservation *at fill time* — and that is the strong
  hole, which is inexpressible (§6). The honest statement: value-carrying promises
  are out of scope, not deferred.
- **Guard expressiveness — multi-party gluing.** The metatheory study
  (`metatheory/docs/GUARDED-HOLES-METATHEORY.md`) PROPOSES — as its one genuinely
  new theorem, **not yet built** (no Lean proof at HEAD) — `guardGluing_iff_iconfluent`:
  that multi-party guards would glue coordination-free IFF each is I-confluent
  (monotone), with non-monotone guards (conservation, capacity) forcing serialized
  consensus (the List-not-Set receipt). If that conjecture holds, a monotone guard
  (a membership proof, a height gate) is cheap and composes while a shared capacity
  guard is expensive — which would bound what `PredCaveat` guards are worth building
  for multi-party holes. Proving it is itself part of this design's work, not a
  standing result to lean on.
- **The circuit witness (§8).** The only VK-affecting item; ember-gated.
- **Open: nesting.** What does the executor do when a `wake` turn itself contains a
  `Promise`? The registry cascade (`dependents`, `pending.rs:49`) handles chained
  resolution, but a fill whose `wake` mints a fresh hole is a fixpoint the
  ConditionalTurnLift residual (§2.5) has not yet folded.
- **Open: cross-federation fills.** `ResolutionCondition::AwaitReceipt` carries an
  optional `federation_id` (`pending.rs:65`) and `RemoteProof` is root-anchored,
  but the broken-promise cascade across a federation boundary
  (`BrokenReason::FederationUnreachable`) is a liveness concern the timeout tooth
  handles only coarsely.

---

## Cross-links (verified to exist)

- `metatheory/Dregg2/Exec/GuardedHole.lean` — the weak hole, proved.
- `metatheory/Dregg2/Substrate/VerbRegistry.lean` — Promise/Notify/React classified.
- `metatheory/Dregg2/Exec/ConditionalTurn.lean`, `ConditionalTurnLift.lean` — the
  promise-pipelining datastructure + its light-client lift.
- `docs/deos/REACTIVE-EFFECTS.md` — the deployed reactive-effect weld.
- `docs/DESIGN-witnessed-nondeterminism-envelope.md` — the agent-loop audit rail
  (a peer promise-shaped concern: replay under a sealed nondeterminism envelope).
- `turn/src/{action.rs,reactive.rs,conditional.rs,pending.rs}`,
  `turn/src/executor/apply.rs` — the deployed Rust.
