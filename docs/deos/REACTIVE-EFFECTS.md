# Reactive Effects — the capacity to make standing commitments, wake, and react

A dregg agent that can only run a turn when prodded is half an agent. The other
half is the capacity to *commit ahead of time* ("when X holds, run this"), to
*wake a peer* ("here is a hole you may react to"), and to *react* to a wake it was
handed — all async, all leaving a verifiable receipt, all one-shot.

This is Track 2 (capacity) of *safely live within dregg*. It is a **weld**: both
halves already exist in the tree, sound but disconnected. The reactive effect is
the first-class vocabulary that joins them, and it is **sound by construction**
because a promise-hole *is* a nullifier — to react is to spend, and the circuit
already refuses a double-spend.

---

## 1. The two halves (grounded, file:line)

### The sound kernel (proven, but not a first-class effect)

`turn/src/pending.rs` — the promise-hole registry:

- `PendingEntry` (`pending.rs:43`) — a turn + its `ResolutionCondition` + dependents
  + a `timeout_height`. **A promise-hole.**
- `ResolutionCondition` (`pending.rs:58`) — `AwaitReceipt` / `AwaitCondition(ProofCondition)` / `AwaitHeight`.
- `PendingTurnRegistry` (`pending.rs:165`) with `submit_pending_at` (`:202`),
  `resolve` (`:241`, **removes the entry** and cascades), `get_pending` (`:327`),
  `check_timeouts` (`:309`).

`turn/src/conditional.rs` — the proof gate that already carries a real nullifier:

- `ProofCondition` (`conditional.rs:54`) — `HashPreimage` / `RemoteProof` / `LocalProof` / `TurnExecuted`.
- `resolve_condition(... used_proof_hashes: &mut HashSet<[u8;32]> ...)` (`:191`) —
  checks timeout, then **the nullifier** (`:206`): a proof hash already in the set
  is refused with `"proof already used"`; a *successful* resolution **inserts** the
  hash (`:221`). This is the double-spend gate, already live and tested
  (`adversarial_proof_replay_attack`, `:1320`).

Lean (proven, `metatheory/Dregg2/...`):

- `Await.commit_resumes_once` (`Await.lean:260`) — a continuation resumes **exactly
  once** on commit (`OneShot.resume` consumes it). One-shot is a *static* invariant.
- `holeFill_binds_in_circuit` (`Exec/GuardedHole.lean:59`) — **the keystone**: a
  successful hole-fill BINDS *both* legs — the δ (the post-state is exactly the
  `stateStep` write) *and* the guard (every `PredCaveat` discharged). A late witness
  is admitted only on terms the eager shape fixed up front.
- `holeFill_rejects_guard_violation` (`Exec/GuardedHole.lean:67`) — fail-closed: a
  violating value does not fill.
- `condTurn_dependency_sound` (`Exec/ConditionalTurn.lean:407`) — topo order is
  respected; a consumer runs after its producer fills the awaited slot.
- `forward_is_handler_commit` (`Exec/ConditionalTurn.lean:602`) — the batch's
  slot-fill *is* `Await.commit_resumes_once` (the await↔executor bridge).

### The live UI (ad-hoc, no kernel backing)

`starbridge-v2/src/swarm.rs` + `starbridge-v2/src/coordination.rs`:

- `NotifyEdge` (`swarm.rs:132`) — A woke B: a committed `EmitEvent` deposited a wake
  in B's `inbox: Vec<NotifyEdge>` (`swarm.rs:278`). Created in `Swarm::run`
  (`swarm.rs:750`), routed through B's held `NotifyCap` (`admits_wake`, `:358`).
- `drain_notify` (`swarm.rs:1127`) — B reacts in its *own* receipted turn (sets an
  ack field), marks the edge `drained = true` (`:1169`). The async A→B causality is
  two independent receipts.
- `NotifyArrow` (`coordination.rs:76`) — the graph view of those deposited edges.

The UI's one-shot is **just a `drained: bool` flag** (`swarm.rs:147`). There is no
kernel-backed registry behind the inbox and no proof nullifier — it is honest but
ad-hoc.

---

## 2. The 1:1 correspondence (the weld)

| UI (ad-hoc, `starbridge-v2`)         | kernel (sound, `turn/`)                                  |
|--------------------------------------|---------------------------------------------------------|
| the `inbox: Vec<NotifyEdge>`         | a cell's view of its `PendingTurnRegistry`              |
| a `NotifyEdge` (a deposited wake)    | a `PendingEntry` (a promise/wake + `ResolutionCondition`)|
| "drain / react" (`drain_notify`)     | `resolve_condition` → `registry.resolve` → fire the turn|
| `drained: bool` (the one-shot)       | entry **removal** on resolve **+** the proof nullifier   |
| `sender_receipt` (provenance link)   | the resolution receipt / `AwaitReceipt` turn hash       |
| `NotifyCap::admits_wake` (topic gate)| the `ResolutionCondition` the react must discharge       |

The UI's inbox and the kernel's registry are the *same object* seen from two sides.
The reactive effect makes that identity first-class.

---

## 3. The first-class effect ADT

`turn/src/reactive.rs` — `ReactiveEffect`:

```rust
pub enum ReactiveEffect {
    /// A standing commitment: run `turn` once `condition` holds. A promise-hole.
    Promise { cell, resolution_condition },          // → registry.submit_pending
    /// A wake from A to B: deposit a promise-hole in B's registry.
    Notify  { from, to, wake, resolution_condition },// → the kernel-backed NotifyEdge
    /// Discharge a deposited hole by presenting its proof. The one-shot spend.
    React   { pending_id, condition, resolution_proof }, // → resolve + the nullifier
}
```

Each maps onto the proven kernel:

- **`Promise`** *is* `PendingTurnRegistry::submit_pending_at` — a held turn awaiting
  its `ResolutionCondition`. (The Lean `holeFill_binds_in_circuit` shape: the hole's
  guard and field are fixed up front; only the resolving value arrives late.)
- **`Notify`** *is* the kernel-backed `NotifyEdge`: A deposits a `PendingEntry` (the
  `wake` turn B commits to run) in B's registry. Where the UI inserts into a
  `Vec<NotifyEdge>`, the effect submits to B's `PendingTurnRegistry`.
- **`React`** *is* `resolve_condition` (the gate + the nullifier) followed by
  `registry.resolve` (which removes the entry and cascades). This is
  `Await.commit_resumes_once` realized in Rust: the hole resumes exactly once.

---

## 4. The soundness argument — a promise-hole IS a nullifier

To **react** is to **spend** the hole. One-shot linearity — react exactly once — is
the SAME double-spend non-membership the circuit already enforces on `noteSpend`
(just proven light-client-sound). So **react-twice = double-spend = already
rejected**, by construction. We do not re-implement the gate; we ride it.

`ReactiveCoordinator::react` (`reactive.rs`) enforces one-shotness at **two
independent teeth**, so neither alone is load-bearing:

1. **Registry removal (TOOTH 1).** `react` first looks up the hole
   (`registry.get_pending`). On a successful spend, `registry.resolve` **removes**
   the entry. A second react finds **no live hole** → `ReactError::AlreadyReacted`.
   The promise-hole is consumed — exactly the `drained` semantics, now kernel-backed.
2. **The proof nullifier (TOOTH 2).** The resolution proof is run through
   `resolve_condition` against the **shared** `used_proof_hashes`. A replayed proof
   is refused with `"proof already used"` (`reactive.rs` → `conditional.rs:206`), and
   the hash is recorded only on success. So even a re-presented proof — on a *fresh*
   hole with the same condition — is refused.

A *failed* react (wrong proof / expired / already-spent proof) **spends nothing**:
the hole stays live (fail-closed), and only genuine spends grow the nullifier. This
mirrors `holeFill_rejects_guard_violation` (`GuardedHole.lean:67`).

The forge-detector that proves this is real (not an unconditional `Err`):

- `react_twice_rejected` — a genuine first react succeeds; the **second** react on
  the same `pending_id` is refused because the entry is **gone** from the registry.
- `replayed_proof_refused_by_nullifier_on_a_fresh_hole` — proves TOOTH 2 alone is
  genuine: a fresh, live hole still refuses an already-spent proof.
- `notify_then_react_resolves_once` — the positive: a genuine notify→react resolves
  once and is **recorded** (a `ResolutionEvent::Resolved` for the hole).
- `wrong_proof_rejected_hole_survives`, `expired_hole_refuses`,
  `react_to_unknown_hole_refused` — the fail-closed envelope.

All six pass (`cargo test -p dregg-turn reactive::`).

---

## 5. The migration: ad-hoc `NotifyEdge` → kernel-backed `PendingEntry`

The starbridge swarm currently:

```
Swarm::run    → inbox.insert(0, NotifyEdge { drained: false, .. })
drain_notify  → inbox[pos].drained = true   // the one-shot is a bool
```

The kernel-backed form (this slice provides the `turn/`-side machinery):

```
Notify → coord.notify(wake, resolution_condition, timeout, height) -> pending_id
React  → coord.react(pending_id, &condition, &proof, height)       -> ReactOutcome
                                                                   | Err(AlreadyReacted)
```

The swarm's `SwarmMember.inbox` becomes a *view* of the member's
`ReactiveCoordinator::registry()`, and `drain_notify` becomes a `react` carrying the
proof the wake's condition demands (for a plain wake, a `HashPreimage` the sender
committed to; for a coordinated turn, a `TurnExecuted` receipt). The `drained: bool`
is then a *projection* of "is this hole still in the registry", not the source of
truth. That wiring is a starbridge-side change (the parallel agent owns nearby cap
routes; this slice keeps the `turn/` machinery self-contained and proven).

---

## 6. What an agent gains

- **Standing orders.** `Promise { when X, run T }` — the agent commits ahead of
  time; the turn fires when (and only when) the condition is discharged, exactly
  once, with a receipt. The deposit/timeout economics (`conditional.rs:45/541/549`)
  already price the standing commitment and reclaim a griefer's slot.
- **Async coordination.** `A.Notify(B)` then `B.React(...)` — A and B coordinate
  with two independent receipts and a visible causal edge, never a joint turn. The
  ocap async-message model, kernel-backed.
- **Soundness for free.** Because react = spend, the reactive vocabulary inherits
  the light-client-unfoolability of the nullifier gate: a light client that verifies
  the batch sees react-twice rejected for the same reason it sees a double-spend
  rejected.

---

## 7. The next slice (named precisely)

This slice delivers the **executor-side** one-shot enforcement (the
`ReactiveCoordinator` + the two-teeth react gate) and the design weld. Two lifts
remain, each named, not parked:

1. **Effect-vocabulary integration.** Add `ReactiveEffect` as a real `Effect`
   variant the `TurnExecutor` dispatches (so `Notify`/`React` are emitted *inside* a
   turn's `CallForest`, not driven by a side coordinator), and replace
   `synthetic_resolution_receipt` (`reactive.rs`) with the genuine executor receipt
   from running the resolved `wake` turn. This is the `execConditionalTurn` /
   `FullForest` / apex-fold wiring the partial-turn memory flags as "WIRE, not
   build."

2. **The circuit witness for `React`.** The Lean obligation **named but not yet
   discharged** for this exact ADT: that a light client verifying a batch bearing a
   `React` sees the promise-hole nullifier grow **exactly as a `noteSpend` does** —
   i.e. `React` refines a `noteSpend` grow-gate step. The shape is already proven
   for guarded holes (`holeFill_binds_in_circuit`, `GuardedHole.lean:59`) and for the
   batch executor (`forward_is_handler_commit`, `ConditionalTurn.lean:602`); the lift
   is to expose `React`'s `pending_id` *as* the nullifier in the effect's circuit
   descriptor so the in-circuit witness binds it. Until then, the Rust gate here is
   the enforcement and the Lean theorems are the spec it answers to.
