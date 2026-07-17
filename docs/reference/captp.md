# CapTP, promises & conditional turns

This subsystem carries dregg turns across federations without round-trip stalls.
A message can be sent to a promise that has **not yet resolved**; it is queued,
then delivered (or cascaded as broken) when the promise settles. The security
invariant is that pipelining is **a latency optimization, not an authority
bypass**: every delivered send is re-checked by the same verified executor that
checks an ordinary turn.

The Rust runtime lives in two crates:

- `captp/` — cross-federation pipelining, sturdy refs, swiss table, GC, handoff,
  store-and-forward, the OCapN netlayer.
- `turn/src/{eventual,conditional,pending}.rs` — the local promise/dependency
  machinery: batched topological execution, STARK-conditional turns, and the
  pending-turn dependency graph.

The semantics are mirrored and proved in Lean under `metatheory/Dregg2/Exec/`
and `metatheory/Dregg2/Spec/Await.lean`, with a differential corpus pinning the
Rust state machine to the proved model.

---

## 1. Promise pipelining (`captp/src/pipeline.rs`)

### The wire and registry types

A pipelined send targets a promise on the receiver's side and names a result
promise on the sender's side:

- `PipelinedMessage { target_promise_id, action, result_promise_id, sender }`
  (`captp/src/pipeline.rs:108`). `result_promise_id: None` is fire-and-forget
  (`captp/src/pipeline.rs:116`).
- `PipelinedAction { method, args, authorization }`
  (`captp/src/pipeline.rs:123`) — `authorization` is opaque bytes the receiver
  re-validates; the pipeline layer never interprets it.
- `PipelinePromiseState` is `Pending | Fulfilled { resolved_cell } | Broken { reason }`
  (`captp/src/pipeline.rs:134`).

`PipelineRegistry` (`captp/src/pipeline.rs:192`) is the per-peer state machine:
per-promise FIFO message queues, per-promise state, and a `next_id` allocator.
Its operations:

- `create_promise` allocates a fresh `Pending` promise with an empty queue
  (`captp/src/pipeline.rs:215`).
- `pipeline_message` queues a send: unknown promise ⇒ `PromiseNotFound`; broken ⇒
  `PromiseAlreadyBroken` (registry unchanged); pending/fulfilled ⇒ FIFO append
  (`captp/src/pipeline.rs:229`).
- `resolve_promise` marks the promise `Fulfilled`, removes and returns the queued
  messages (`captp/src/pipeline.rs:259`).
- `break_promise` marks the promise `Broken`, drains the queue **delivering
  nothing**, and cascades: each queued message with a `result_promise_id`
  produces a `BrokenPromiseNotification`, and if that result promise is local it
  is recursively broken (`captp/src/pipeline.rs:287`).
- `pipeline_chain` builds a chain where each step targets the previous step's
  result promise, returning the final promise id; an empty chain is
  `EmptyChain` (`captp/src/pipeline.rs:333`).

### The verified drain order

`resolve_promise` does not return the native FIFO order blindly. It calls
`verified_drain_reorder` (`captp/src/pipeline.rs:52`), which queries the verified
Lean gate (`dregg_captp_pipeline_resolve`) for the authoritative drain order and
reassembles the messages in that order. When the gate is unavailable (FFI-free
target, archive lacks the export, malformed reply) it falls back to the native
FIFO drain (`captp/src/pipeline.rs:53`, `:65`, `:81`). The gate is reached
through `CaptpVerifiedGate::pipeline_resolve` (`captp/src/verified_gate.rs:27`),
gated on `distributed_exports_available` (`captp/src/verified_gate.rs:19`).

### Cross-federation bridge

`CrossFedPipelineBridge` (`captp/src/pipeline.rs:489`) holds a `PipelineRegistry`
per remote peer plus a `local` registry, an outbox of wire messages, and an
optional `local_federation` identity. `with_local_federation`
(`captp/src/pipeline.rs:525`) stamps a concrete sender on every outbound send;
without it, `outbound_sender` falls back to the `[0;32]` placeholder
(`captp/src/pipeline.rs:791`). Key flows:

- `pipeline_to_remote` creates a local result promise and enqueues a
  `PipelineToPromise` wire message (`captp/src/pipeline.rs:552`).
- `on_remote_resolution` / `on_remote_breakage` settle a local promise
  (`captp/src/pipeline.rs:628`, `:641`).
- `on_pipeline_message` queues an incoming send against our local or the peer's
  registry, implicitly creating the promise if unknown
  (`captp/src/pipeline.rs:654`).
- `resolve_local_promise` / `break_local_promise` settle one of our promises and
  collect every peer's queued sends / break notifications
  (`captp/src/pipeline.rs:718`, `:743`).

The bridge is consumed by the wire server: `CaptpState.pipeline_bridge` is built
via `with_local_federation` (`wire/src/server.rs:1000`), inbound pipelined
messages dispatch through `on_pipeline_message` (`wire/src/server.rs:2802`), and
local resolution drains via `resolve_local_promise` (`wire/src/server.rs:1081`).

### Wire messages

`PipelineWireMessage` (`captp/src/pipeline.rs:414`) carries the four cross-fed
messages: `PipelineToPromise`, `PromiseResolved`, `PromiseBroken`, and
`PipelineResult` (success carries a `cell_id` + receipt hash; failure carries an
error string — `PipelineResultValue`, `captp/src/pipeline.rs:464`).

---

## 2. The Lean model & soundness (`metatheory/Dregg2/Exec/CapTPPipeline.lean`)

The Lean module models pipelining in two layers, both `#assert_axioms`-clean on
the three standard kernel axioms (`CapTPPipeline.lean:588`–`603`).

**The executable drain** (each delivered send IS a verified turn):

- `drainStep k s = exec k s.turn` — one queued send is applied through the same
  fail-closed kernel executor `exec` (`CapTPPipeline.drainStep`, `:83`).
- `drainAll` folds the queue in FIFO order, short-circuiting to `none` on the
  first rejected send (`CapTPPipeline.drainAll`, `:92`).
- `resolve` dispatches: `fulfilled` ⇒ `drainAll`; `broken` ⇒ return state
  unchanged (`CapTPPipeline.resolve`, `:100`).

Proved laws over the drain:

- `drainAll_preserves_caps` — draining never grows the capability table; no send
  can acquire authority the sender did not hold (`CapTPPipeline.drainAll_preserves_caps`).
- `drainAll_head_authorized` + `drainAll_tail` — every committed send was
  authorized at the moment it applied (`CapTPPipeline.drainAll_head_authorized`).
- `overAuthorized_send_rejected` / `drainAll_aborts_on_unauthorized_head` — a
  forged/over-authorized send is rejected on drain; one such send anywhere aborts
  the whole batch (`CapTPPipeline.overAuthorized_send_rejected`,
  `.drainAll_aborts_on_unauthorized_head`).
- `break_freezes_state` — a broken promise returns the state unchanged: no
  orphaned grant (`CapTPPipeline.break_freezes_state`).
- `drainAll_conserves` — a drained pipeline conserves total supply
  (`CapTPPipeline.drainAll_conserves`).
- `drain_realizes_seam` — drain success ⇔ the executor re-checked
  `authorizedB k.caps turn` (`CapTPPipeline.drain_realizes_seam`).

**The registry state machine** (`namespace Registry`, `CapTPPipeline.lean:316`):
a faithful `Nat`-keyed mirror of `PipelineRegistry` with `createPromise`,
`pipelineMessage`, `resolvePromise`, `breakPromise`
(`CapTPPipeline.Registry.createPromise` … `.breakPromise`). Proved:

- `resolve_clears_queue` — after resolve the queue is empty, promise `Fulfilled`
  (`CapTPPipeline.Registry.resolve_clears_queue`).
- `resolve_preserves_fifo` — the drained order IS insertion order, oldest-first
  (`CapTPPipeline.Registry.resolve_preserves_fifo`).
- `broken_target_rejects_queue` — queueing onto a broken promise is rejected,
  registry unchanged (`CapTPPipeline.Registry.broken_target_rejects_queue`).

**The differential corpus** ties the Lean model to the running Rust. A program
`pipelineDifferentialCorpus` (`CapTPPipeline.lean:549`) exercises create → FIFO
queue ×2 → resolve → re-queue-on-fulfilled → break → queue-on-broken. Its
observable column `(queuedCount, stateTag, ok)` is proved by `decide`
(`CapTPPipeline.Registry.pipelineDifferentialCorpus_observable`) and the FIFO
drain order by `pipelineDifferentialCorpus_drain_order`. The Rust harness
`captp/tests/pipeline_registry_differential.rs` replays the SAME corpus against
the real `PipelineRegistry` and asserts the triples match (`state_tag` mirrors
the Lean `stateTag`, `pipeline_registry_differential.rs:33`, `:59`). A drift on
either side breaks: the runtime triples diverge, or the Lean `decide` trips at
build.

### Abstract seam (`metatheory/Dregg2/Exec/CapTP.lean`)

`PipelinedCall` (`CapTP.lean:90`) carries the authorization as a `Spec.Guard`.
`pipelining_preserves_seam` (`CapTP.pipelining_preserves_seam`) proves the
delivered call's authorization obligation is **exactly** the queued call's —
resolution moves `Pending → Fulfilled`, it does not discharge the guard.
`pipelining_undischarged_stays_undischarged` is the attacker-facing
contrapositive: pipelining onto a promise you cannot authorize gains nothing.
The chain structure and break cascade are connected to the await dataflow DAG:
`pipeline_chain_is_dataflow_edge` and `pipeline_break_cascades`
(`CapTP.pipeline_chain_is_dataflow_edge`, `.pipeline_break_cascades`) reuse
`Spec.Await.PromiseGraph.broken_promise_propagates_trans`.

---

## 3. Local batched execution (`turn/src/eventual.rs`)

This module is **synchronous, local** batched execution — not E-style async
pipelining (`eventual.rs:1`, `:11`). Turns are submitted together, topologically
sorted, and run in causal order; earlier outputs feed later turns.

- `EventualRef { source_turn, output_slot, federation_id }`
  (`eventual.rs:24`) — a reference to a value a pending turn will produce.
  `federation_id: Some(..)` marks a remote source the executor must wait on
  (`eventual.rs:49`, `.is_remote` `:58`).
- `Target` is `Concrete(CellId) | Eventual(EventualRef)` (`eventual.rs:70`).
- `TurnOutput` records what a turn produced for resolution:
  `GrantedCapability | CreatedNote | StateUpdate | CreatedCell`
  (`eventual.rs:119`).
- `Pipeline { turns, dependencies, atomic }` (`eventual.rs:283`).
  `topological_order` returns a `CycleError` on a dependency cycle
  (`eventual.rs:315`); `atomic` means if any turn fails, previously committed
  turns roll back (`eventual.rs:289`). `PipelineBuilder` is the fluent builder
  (`eventual.rs:431`).

Lean: `ConditionalTurn.lean` models a batch as `ConditionalBatch` (nodes + edges,
`ConditionalTurn.lean:90`). `topoOrder` is a Kahn topological sort
(`ConditionalTurn.topoOrder`, `:169`); `execConditionalTurn` runs the batch
all-or-nothing, returning `none` on cycle or any node failure
(`ConditionalTurn.execConditionalTurn`, `:200`). Proved:
`condTurn_atomic` (failure ⇒ no post-state, input untouched,
`ConditionalTurn.condTurn_atomic`), `condTurn_conserves`
(`.condTurn_conserves`), `condTurn_dependency_sound` (`.condTurn_dependency_sound`),
and `condTurn_eventualref_resolved` (`.condTurn_eventualref_resolved`). The Kahn
loop is shown complete on acyclic batches (`topoOrder_some_of_acyclic`) and a
`none` topo result implies cyclic (`topoOrder_none_imp_cyclic`).
`ConditionalTurnLift.lean` lifts authority-only / balance-value-only nodes to the
asset-indexed executor and proves agreement and conservation
(`ConditionalTurnLift.execFullTurnA_lift_authority`, `.execFullA_toA_mint_conserves`).

---

## 4. STARK-conditional turns (`turn/src/conditional.rs`)

A `ConditionalTurn` does not execute until a proof satisfying its condition is
presented before a timeout height; otherwise it expires with no state change
(`conditional.rs:1`). This generalizes an HTLC: any provable statement, not just
a hash preimage, can gate execution (`conditional.rs:13`).

- `ProofCondition` (`conditional.rs:54`): `HashPreimage` (BLAKE3 preimage),
  `RemoteProof` (a STARK proof against a remote federation's attested root),
  `LocalProof` (a STARK proof with expected public inputs), `TurnExecuted`
  (present a turn receipt).
- `ConditionalTurn { turn, condition, timeout_height, submitted_at, deposit_amount }`
  (`conditional.rs:88`). A reservation deposit is deducted at submission, refunded
  on resolution and burned on timeout (`conditional.rs:97`,
  `refund_conditional_deposit` `:541`, `burn_conditional_deposit` `:549`).
- `compute_conditional_deposit = BASE_CONDITIONAL_DEPOSIT + PER_BLOCK_DEPOSIT *
  blocks_until_timeout` (`conditional.rs:45`; constants at `:35`, `:38`).
- `resolve_condition` (`conditional.rs:191`) checks timeout, a proof **nullifier**
  to prevent reuse (`compute_proof_hash`, `conditional.rs:228`), proof-type
  match, AIR-name match, root freshness against `max_root_age`, and cryptographic
  STARK verification. For `TurnExecuted`, the receipt's `executor_signature` must
  verify against a known executor key, blocking fabricated receipts
  (`conditional.rs:188`). Results: `Resolved | Pending | Expired |
  InvalidProof(..)` (`ConditionalResult`, `conditional.rs:151`).

This realizes cross-federation atomicity: Fed A's turn executes iff Fed B's proof
arrives before height H, and symmetrically — both execute, or both expire
(`conditional.rs:6`).

---

## 5. Pending turns & broken-promise propagation (`turn/src/pending.rs`)

`PendingTurnRegistry` (`pending.rs:165`) extends the local pipeline with REAL
distributed coordination: a turn can be `Pending` awaiting external resolution,
EventualRefs can name turns on other federations, and a break propagates to all
dependents (`pending.rs:1`).

- `PendingEntry { turn, condition, dependents, submitted_at, timeout_height }`
  (`pending.rs:43`).
- `ResolutionCondition` (`pending.rs:58`): `AwaitReceipt { turn_hash,
  federation_id }` (remote when `federation_id` is `Some`), `AwaitCondition(ProofCondition)`,
  `AwaitHeight(u64)`.
- `BrokenReason` (`pending.rs:84`): `TurnRejected | Timeout | FederationUnreachable
  | DependencyBroken(Box<BrokenReason>)`.
- `resolve` (`pending.rs:241`): on `Resolved`, cascade to dependents whose
  condition is now met, emitting `ReadyToExecute` events — the node must actually
  execute and call `resolve` again with a real receipt (the registry never
  fabricates receipts, `pending.rs:268`). On `Broken`, `propagate_broken`
  recursively breaks every dependent with `DependencyBroken` (`pending.rs:361`).
- `check_timeouts` breaks every entry past its `timeout_height`
  (`pending.rs:309`); `check_height_conditions` reports entries whose `AwaitHeight`
  is met for the node to execute (`pending.rs:388`).

This registry is held in node state as `pending_turns`
(`node/src/state.rs:146`).

The Lean dataflow spec is `metatheory/Dregg2/Spec/Await.lean`: a `Promise` carries a `fulfilled`
flag (`Await.Promise`, `:253`); a `PromiseGraph` is the dependency DAG
(`Await.PromiseGraph`, `:266`) with `Acyclic` / `Depends`. `broken_promise_propagates`
and `broken_promise_propagates_trans` (`Await.PromiseGraph.broken_promise_propagates`,
`.broken_promise_propagates_trans`, both `#assert_axioms`-clean at `Await.lean:478`)
prove a broken promise's transitive dependents cannot resolve.

---

## 6. Guarded holes (`metatheory/Dregg2/Exec/GuardedHole.lean`)

A guarded hole is the formal "promise-hole as a predicated late-fill" object. The
study (`metatheory/docs/GUARDED-HOLES-METATHEORY.md`) splits it:

- the **weak** guarded hole — a `Pred` guard on a late-filled `EventualRef` slot,
  discharged at fill time — is built here as a first-class object;
- the **strong** guarded hole — a hole in a conservation/authority position (an
  undetermined δ) — is deliberately NOT built: it is inexpressible in dregg (no
  non-zero-δ primitive), safe by inexpressibility (`GuardedHole.lean:4`).

`GuardedHole { field, actor, target, guard }` fixes the **shape** eagerly; only
the **value** arrives late (`GuardedHole.lean:37`). `fillGuarded h s n` installs
the late value via the guarded `put` `predStateStepGuarded`, committing the write
iff every caveat of `h.guard` admits the transition, fail-closed
(`Holes.fillGuarded`, `:48`). The keystone `holeFill_binds_in_circuit`
(`Holes.holeFill_binds_in_circuit`) proves a successful fill binds BOTH its δ
(the post-state is exactly the `stateStep` write, no hidden mutation) AND its
guard (every caveat discharged). `holeFill_rejects_guard_violation` is the
negative tooth: a value violating the guard does not fill
(`Holes.holeFill_rejects_guard_violation`). Both are `#assert_axioms`-clean
(`GuardedHole.lean:88`).

---

## Map: Rust ↔ Lean

| Concern | Rust | Lean |
| --- | --- | --- |
| pipelined send delivered = verified turn | `pipeline.rs` `resolve_promise` | `CapTPPipeline.drainStep` / `drainAll` |
| no authority amplification on drain | re-validated `authorization` | `CapTPPipeline.drainAll_preserves_caps` |
| broken promise installs nothing | `break_promise` (no delivery) | `CapTPPipeline.break_freezes_state` |
| FIFO drain order | `verified_drain_reorder` + native FIFO | `CapTPPipeline.Registry.resolve_preserves_fifo` |
| registry state machine ↔ runtime | `PipelineRegistry` | `CapTPPipeline.Registry` + `pipelineDifferentialCorpus` |
| authorization survives resolution | `authorization` bytes unchanged | `CapTP.pipelining_preserves_seam` |
| local batched execution | `eventual.rs` `Pipeline` | `ConditionalTurn.execConditionalTurn`, `condTurn_atomic` |
| conditional/STARK-gated turn | `conditional.rs` `resolve_condition` | `Spec.Await.Conditional` |
| pending/broken propagation | `pending.rs` `PendingTurnRegistry` | `Spec.Await.PromiseGraph.broken_promise_propagates_trans` |
| weak guarded hole | (the `Pred`/`EventualRef` late-fill) | `Holes.holeFill_binds_in_circuit` |

The through-line: **a pipelined send carries the authority its sender holds and
nothing more; resolution delivers it to the same fail-closed executor; a break
delivers nothing.** Pipelining buys latency, not authority.
