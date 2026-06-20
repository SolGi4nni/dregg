# Partial-Turn Lift — the held promise as a first-class continuation

A turn is the exercise of an attenuable proof-carrying token over owned state, leaving a
verifiable receipt. A *partial* turn is that same exercise with a hole in it: a value it
will consume is not yet known, but the SHAPE of how it will be consumed — which field, whose
write, under which predicate — is fixed now. This document specifies the lift that makes a
held partial turn a first-class object the cockpit can stage, inspect, and resume.

## 1. What already exists (census, not invention)

The promise-pipelining substrate is built and proven; the lift WIRES it, it does not build it.

- **`turn::eventual`** (`turn/src/eventual.rs`) — `EventualRef { source_turn, output_slot,
  federation_id }`, `Target::{Concrete(CellId), Eventual(EventualRef)}`, `TurnOutput`,
  `Pipeline { turns, dependencies, atomic }`, `PipelineBuilder`. A turn whose `Target` is
  `Eventual` is a turn with a hole: it names *the slot a future turn's output fills*.
- **`Dregg2/Exec/ConditionalTurn.lean`** — `ConditionalBatch { nodes, edges }`, `Slots := Nat
  → Bool`, `execConditionalTurn` — Kahn-topological all-or-nothing execution; an open
  `EventualRef` edge IS a hole, its fill IS the producer node's commit-arm slot write. Proven:
  run order respects every edge (no use-before-define).
- **`Dregg2/Exec/GuardedHole.lean`** — the keystone. `GuardedHole { field, actor, target,
  guard }` (the EAGER SHAPE) + `fillGuarded h s n` (= `predStateStepGuarded`, the guarded
  `put`). The theorem with teeth: **`holeFill_binds_in_circuit`** — a successful fill binds
  BOTH its δ (post-state is exactly the `stateStep` write, no hidden mutation) AND its guard
  (every `Pred`-caveat discharged) into the committed post-state. The negative tooth,
  **`holeFill_rejects_guard_violation`** — a value violating the guard does NOT fill
  (fail-closed). Determination is EAGER, witness is LAZY.
- **`captp::pipeline`** — promise pipelining drained through the verified kernel executor;
  no-amplification + break-cascade over the executable drain.
- **`World` suspend gate** (`starbridge-v2/src/world.rs`) — `suspend()` / `resume(ResumeMode)`
  / `pending: VecDeque<Turn>`. A turn submitted while suspended STAGES into `pending` (the
  continuation) and commits on `resume(Drain)`.

## 2. The gap, named precisely

The cockpit's held continuation today is a **flat queue of fully-concrete turns**
(`VecDeque<Turn>`). Every staged turn already knows every value it will write. There is no way
to stage a turn that *awaits* a value — to hold a promise. The promise-pipelining structures
(`Pipeline`, `EventualRef`, `GuardedHole`) live in `turn::eventual` and in Lean, but the
suspend continuation cannot carry them.

The lift is therefore TWO surfaces:

1. **The held-promise continuation** — make the suspended continuation able to carry a
   `Pipeline`-with-holes (turns with unresolved `EventualRef`/`Target::Eventual`), not only a
   `VecDeque<Turn>`. Staging a turn with an open hole HOLDS A PROMISE; resume FILLS the hole
   (binding δ and guard, fail-closed) and only then drains.
2. **The effect-vocabulary surface** — an effect whose payload is a (partial) `ConditionalBatch`
   so a turn can WITNESS or EMIT a partial turn. (Design only here; see §6.)

## 3. The UX of a held promise

A held promise has a small, total lifecycle the cockpit renders directly:

```
        stage(turn with hole)            fill(value)                drain
  ┌──────┐ ─────────────────▶ ┌────────┐ ──────────────▶ ┌────────┐ ─────▶ commit
  │ EMPTY│                    │  HELD  │   (guard admits) │ READY  │
  └──────┘                    └────────┘                  └────────┘
                                   │ fill(value), guard REJECTS
                                   ▼
                              stays HELD  (fail-closed; the late witness
                                           cannot escape the eager shape)
```

- **EMPTY** — no continuation staged.
- **HELD** — a partial turn is staged with ≥1 unresolved hole. The cockpit shows the eager
  shape of each hole: which field it lands in, whose write, under which guard. The value is the
  only unknown. The world head is frozen (suspend gate); nothing commits.
- **READY** — every hole filled with a guard-admitted value. The continuation is now a concrete
  `Pipeline` (no `Eventual` targets remain) and may drain through the normal `commit_turn` gate.
- A fill whose value VIOLATES the hole's guard does NOT advance the state — the hole stays open,
  the continuation stays HELD. This is `holeFill_rejects_guard_violation`: fail-closed, never a
  silent admit.

The held promise is the UX shadow of `holeFill_binds_in_circuit`: you can stage a promise, but
you can only RESOLVE it on the terms the hole fixed up front.

## 4. Connections (the same object in three clothes)

- **A beacon value** (the resharing-chains workflow / forward-secure common-secret chains) is a
  promise resolved at the tick: a hole filled at quorum-after-t. The eager shape (which field
  the beacon lands in, under the threshold guard) is fixed when the chain is staged; the value
  arrives at the tick.
- **A time-lock** is a hole whose guard is a deadline predicate (`Conditional.resolve`): held
  until the clock admits, then filled.
- **A CapTP promise** (`captp::pipeline`) is a hole whose producer is a remote send; the
  `EventualRef.federation_id` names the remote federation whose receipt fills it.

All three are the same structure: a lazy witness over an eager shape, bound at fill.

## 5. Why STRONG holes stay inexpressible (the load-bearing line)

This lift carries ONLY the weak guarded hole — a `Pred` guard on a late VALUE. It deliberately
does NOT introduce a hole in a conservation or authority position (an undetermined δ, a lazy
SHAPE). A continuation that could stage a turn whose *contribution to conservation* is unknown
would let an undetermined-δ turn ride into the drain. dregg forbids this by inexpressibility:
there is no non-zero-δ primitive, joint turns take the whole agreeing cone, authority must be
in-circuit. The held-promise model enforces the same line: a hole carries a VALUE and a guard,
never an open δ-shape. Failure is by inexpressibility (safe), not by a silent admit.

## 6. The effect-vocabulary surface (design, deferred)

To let a turn WITNESS/EMIT a partial turn, the per-effect forest (`FullForestA`) the kernel and
the light-client apex fold over would need a node carrying a (partial) `ConditionalBatch`. The
open questions (honest, from the partial-turn memory):

1. A new `FullAction` variant carrying a `ConditionalBatch`, vs. a reflection of the existing
   `execConditionalTurn` into the forest. What does the executor do when an effect's payload is
   itself a batch of turns (nesting / fixpoint)?
2. Is the CIRCUIT in scope? The apex folds `FullForestA`; whether a batch-bearing effect can be
   given a descriptor + a refinement rung is the real feasibility question, not assumed.
3. How do slot-fills commit in the content-addressed record world (`RecChainedState` /
   `recTotal`)?

This surface is NOT built in this slice. The slice below builds surface (1): the headless
held-promise continuation, which is the part with a clean, bounded, fail-closed semantics.

## 7. The slice that ships

`starbridge-v2/src/held_promise.rs` — a gpui-free headless model of a held-promise
continuation. It mirrors the real shapes (`EventualRef`-style slot references, the eager
guarded-hole shape, fail-closed fill) without pulling in the executor, so it is testable in
isolation and both-polarity tested:

- `HeldPromise` — a continuation that may carry open holes; states EMPTY / HELD / READY.
- `Hole { field, actor, target, guard }` — the eager shape (mirrors `GuardedHole`).
- `Guard` — a minimal two-valued predicate over the fill value (mirrors a `PredCaveat`,
  enough to make the tooth bite TRUE and FALSE).
- `fill(slot, value)` — binds the value into the slot IFF the guard admits; fail-closed
  otherwise (the hole stays open, the state is untouched).
- `is_ready()` — true iff no holes remain open; only then may the continuation drain.

Both-polarity teeth: a guard-admitted value FILLS and advances toward READY; a guard-violating
value is REJECTED and the continuation stays HELD with the hole still open. A continuation with
an open hole is NOT ready (cannot drain) — the structural fail-closed.

## 8. Wiring (report only — not edited here)

The slice is a NEW file with NO edits to shared `lib.rs` / `Cargo.toml`. To wire it in:

- Add to `starbridge-v2/src/lib.rs`: `pub mod held_promise;` (alongside `pub mod world;`).
- No new dependencies (`std` only; `serde` already in the workspace if serialization is wanted
  later — the slice does not require it).

The cockpit integration (making `World::pending` able to hold a `HeldPromise` rather than only
a `VecDeque<Turn>`) is the follow-on: replace the flat queue with a continuation that may carry
a held promise, fill at resume, drain only when READY. That edit touches shared `world.rs` and
is left to the main loop to sequence (the receipt-chain regression on the commit path is being
cleared in parallel; the held-promise model is independent of it).
