# Finalized execution outcome and acknowledgement law

**Status:** corrective protocol design; the live dispatcher does not yet satisfy this law.  The
exact FNSP-v3 splice is unsafe against operational failure until this repair lands, even while it
remains solo-only.

## The defect at HEAD

`BlocklaceHandle::poll_finalized_blocks` computes the pending identities, converts them into
`FinalizedBlock` work, and immediately calls `ExecutionCursor::mark_executed`.  Actual application
happens later in `spawn_finality_executor`.  At the end of the batch,
`persist_blocklace_state` writes that served-id set independently of application outcomes.

This means “handed to a function once” is currently treated as “durably committed or durably
rejected.”  They are not equivalent.

The exact-v3 path exposes the failure sharply.  `execute_live_exact_fnsp_v3` returns one
`Result<(), String>` for all failures.  Its caller stores every error under
`exact-fnsp-v3-finalization-refused`, including errors caused by local snapshot movement, a proof
worker panic/cancellation, history/store I/O, or the atomic commit itself.  The loop then persists
the already-served cursor.  A valid finalized block can therefore be permanently consumed because
one validator experienced a local operational failure.

## The law

A finalized actionable block may enter the executed identity set only after one of exactly two
durable terminal outcomes:

```text
Committed(finalized state transition, receipt, side state, block id)
DeterministicallyRejected(block id, payload digest, stable consensus reason)
```

Both outcomes are replayable consensus facts.  Neither is a log message or an in-memory return
value.

A retryable operational failure does not acknowledge the block:

```text
RetryableOperational(local/store/worker failure)  => pending, stop later application
FatalIntegrity(corrupt authority or impossible invariant) => fail stop, do not acknowledge
```

The dispatcher must not execute a later finalized state transition after an earlier one is pending
retry.  That would apply the total order with a hole.

## Typed outcome

The finalized application boundary returns a non-string enum such as:

```text
FinalizedExecutionOutcome
  Committed { block_id, durable_ordinal }
  DeterministicallyRejected { block_id, reason_code }
  RetryableOperational { block_id, error }
  FatalIntegrity { block_id, error }
```

Payload decoding, canonical authorization, proof invalidity under consensus-owned inputs, expired
under authenticated consensus time, and deterministic state precondition failure may produce
`DeterministicallyRejected`.  Worker join errors, local snapshot races, missing local history,
database errors, unavailable verifier archives, and persistence failures do not.  The exact route
must preserve this distinction through proof preparation, off-lock execution, finalization, and
the outer dispatcher; `Result<(), String>` is not an authority boundary.

## Acknowledgement protocol

1. `poll_finalized_blocks` becomes a pure planner.  It observes the tau order and returns pending
   candidates without mutating the executed set.
2. The finality executor processes candidates sequentially.
3. A committed turn's existing atomic commit record is its durable outcome journal row: it already
   binds `block_id` to the state/receipt transaction.
4. A deterministic rejection is written to a versioned outcome table in one transaction.  A
   rejected block is acknowledged only after that transaction returns success.
5. After either terminal durable outcome, update the in-memory identity cursor.  A crash between
   the durable write and this projection update is harmless: restart reconstructs executed turn
   ids from committed records plus durable rejection ids.
6. On `RetryableOperational`, leave the identity pending and stop the batch at that block.  Retry
   on the next wake/backoff without applying successors first.
7. On `FatalIntegrity`, stop the finality executor or node loudly.  Never transmute corruption into
   a consensus payload verdict.

`persist_blocklace_state` remains useful for DAG metadata and consensus-inert identities, but its
best-effort served-id write cannot be authority for an actionable turn.  Turn restart authority is
the union of atomically committed `CommitRecord.block_id` values and atomically persisted
deterministic-rejection ids.

Membership and checkpoint actions should converge onto the same law: their acknowledgement must
follow an idempotent durable state outcome.  The turn cut is first because it can mutate ledger,
receipt, note, exact, and executor consensus state.

## Ordering under retry

The cursor remains identity-based; this repair does not return to an index.  Let `P` be pending
blocks in the current tau order.  Process the longest prefix of `P` whose elements reach durable
terminal outcomes.  If element `P[i]` is retryable, acknowledge none of `P[i..]`.  A later honest
catch-up insertion is still found by identity on the next poll, while no already committed identity
is re-applied.

## Acceptance gates

1. Inject a generic commit-store failure: no receipt/state/event/rejection or executed id appears;
   the same block is returned by the next poll.
2. Inject exact proof-worker failure and exact redb failure: neither produces a payload rejection;
   both retry the same identity.
3. Place two finalized turns in one batch and fail the first operationally: the second does not
   execute until the first reaches a terminal durable outcome.
4. Persist an invalid SignedTurn rejection, crash before RAM cursor update, restart, and prove it
   is not re-executed.
5. Commit a valid turn, crash before RAM cursor update, restart, and prove commit-log recovery
   acknowledges it exactly once.
6. Fail rejection persistence: the block stays pending and no served-id persistence can hide it.
7. Prefix-shift/catch-up tests remain green with the delayed acknowledgement protocol.
8. Exact first activation plus first frame is either one committed terminal outcome or remains
   pending with no activation, frame, receipt, faithful edge, executor side state, or cursor row.

## Code ownership

The repair owner needs these files as one coherent cut:

- `node/src/execution_cursor.rs`: separate pending observation from terminal acknowledgement.
- `node/src/blocklace_sync.rs`: make polling non-consuming; introduce the typed outcome, sequential
  stop-on-retry loop, and post-durable ACK.
- `node/src/signed_turn_validation.rs`: retain stable deterministic reason codes without absorbing
  operational errors.
- `persist/src/commit_log.rs` and `persist/src/blocklace_store.rs`: expose committed/rejected block
  identities as the restart authority; persist rejection and its outcome atomically.
- `node/src/exact_fnsp_v3_execution_authority.rs` and
  `node/src/exact_fnsp_v3_finalization.rs`: preserve proof-invalid versus operational/store failure
  types through the exact route.

The active exact atomic-weld lane should not independently redesign the global cursor.  It should
return the typed terminal/retryable result and let this owner move acknowledgement.  Until then,
the live exact route must not be described as operationally crash/retry complete.
