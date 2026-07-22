# Consensus time and finalized receipt identity

**Status:** consensus defect and flag-day repair contract.  The current finalized-turn executor is
not deterministic across validators.  This is below FNSP-v3/v4 and affects ordinary turns as well
as exact frames.

## Ground truth at HEAD

`node/src/blocklace_sync.rs::execute_finalized_turn` constructs a fresh `TurnExecutor` and calls
`executor_setup::configure_turn_executor`.  That helper calls `SystemTime::now()` and installs the
result as `executor.current_timestamp`.  The finalized block and its signed payload carry no
consensus timestamp, and the finalized path does not overwrite the local value before execution.

That local value is consensus-observable in two ways:

1. `TurnReceipt::receipt_hash` hashes `receipt.timestamp`.
2. Execution consults `current_timestamp` for `valid_until`, capability expiry, refresh/attenuation,
   rate windows, derived-record creation times, and other stateful branches.

Consequently, two honest validators can derive different receipt-chain heads from the same block.
At a deadline boundary they can derive different accept/reject outcomes or successor states.  A
signer-independent exact-frame envelope does not close this lower seam.

## The law

Finalized execution is a pure function of consensus state and the finalized block:

```text
execute_finalized(pre_state, finalized_block, consensus_context)
  = (post_state, finalized_receipt_core)
```

No local clock, local signer, scheduling instant, receipt encoding, or process-restart instant may
occur in the transitive input of the result.  Wall time may guide mempool admission and block
production; it cannot decide replay or finalized state.

## Flag-day carrier: consensus-authenticated time

Introduce versioned turn-bearing block payloads whose canonical bytes include a
`consensus_unix_seconds: i64`.  Because the block signs the payload hash, this value is authenticated
by the block creator and becomes common input once the block is finalized.  Retire raw
`Payload::Turn` and the current timestamp-less `TurnBundle` from production after the flag day;
legacy rows remain replayable under their historical version.

The time claim is not accepted merely because one producer signed it.  Blocklace admission checks
deterministic causal rules:

- it is at least the maximum consensus time of every predecessor;
- it is no more than a protocol constant beyond that maximum; and
- a block with no predecessor starts from a federation-genesis time anchor committed by genesis,
  never from the receiving node's clock.

These checks are functions of authenticated DAG data and genesis configuration, so every honest
validator reaches the same verdict.  A local future-drift check may refuse to *produce* or relay a
suspicious proposal as policy, but it must not be the consensus validity predicate: nodes on
opposite sides of a wall-clock boundary cannot be allowed to disagree about block validity.

The finalized dispatcher carries a typed `FinalizedExecutionContextV1` containing at least
`block_id`, the tau/finality round, finalized ordinal, and authenticated consensus time.  It sets
the executor time from that context after ordinary executor configuration and before any
authorization, expiry check, proof statement reconstruction, or mutation.  Re-execution and crash
recovery reconstruct the same context from the stored block, never from `SystemTime::now()`.

## Finalized receipt core

Introduce `FinalizedReceiptCoreV1`, a strict canonical projection containing:

- finalized block id, federation/committee epoch, tau round, and finalized ordinal;
- authenticated consensus time;
- turn, forest, agent, and federation identities;
- pre/post state and effects commitments;
- deterministic cost/action counts and receipt predecessor identity; and
- every deterministic routing, derivation, event, disclosure, and capability-consumption field
  currently bound by `TurnReceipt::receipt_hash`.

Its id is:

```text
H("dregg-finalized-receipt-core-v1", canonical(FinalizedReceiptCoreV1))
```

Local executor signatures and any local observation metadata live in a separate envelope over this
id.  Receipt-chain heads, exact-frame cores, attested roots, replay indexes, federation receipts,
and conditional `TurnExecuted` predicates use the finalized id.  They do not use postcard bytes or
a receipt hash minted before finalization.

The existing `TurnReceipt::receipt_hash` domain must not silently acquire this new meaning.  Either
replace consensus consumers with the typed finalized id or bump the receipt domain and wire format
at the same flag day.  Old receipts remain verifiable only under their old domain.

## Deployment order

1. Add the versioned signed payload time carrier, genesis anchor, and deterministic predecessor
   validation to `blocklace/src/finality.rs`.
2. Preserve the source block's context through `FinalizedBlock::Turn` in
   `node/src/blocklace_sync.rs`; never discard it into only `(block_id, bytes)`.
3. Add `FinalizedExecutionContextV1` and make the finalized executor require it.  Keep
   `wall_clock_secs()` only for submission/mempool policy and non-consensus observations.
4. Add the finalized receipt core/id in `turn`, then migrate receipt heads, exact frames,
   conditional predicates, attested roots, and persistence atomically.
5. Make finalization the only production mint for authoritative receipts.  A speculative local
   receipt may be displayed as tentative evidence but cannot advance a consensus chain.
6. Version-gate legacy timestamp-less payloads; do not reinterpret stored history.

## Hostile acceptance gates

The repair is incomplete until focused tests establish:

1. Two executors with different wall clocks replay one finalized block to byte-identical successor
   state and finalized receipt id.
2. A turn at exactly the expiry boundary cannot split accept/reject across validators.
3. Capability expiry, refresh, rate-window, reactive, and derivation timestamps use the carried
   consensus time.
4. Mutating consensus time changes the block id/signature and finalized receipt id.
5. A timestamp below a predecessor, above the deterministic forward bound, or inconsistent with
   the genesis anchor is refused identically by every validator.
6. Restart reconstructs the same execution context and receipt-chain head without reading the
   local clock.
7. A timestamp-less legacy payload cannot enter the post-cutover production path.
8. Exact v4 frame ids are identical under different local clocks and signing keys.

## Ownership boundary

This is a cross-cut below the current exact-frame implementation.  The implementation lane should
own `blocklace/src/finality.rs`, the finalized-context plumbing in `node/src/blocklace_sync.rs`, and
the new receipt core in `turn`.  The active exact-v3 atomic splice should consume the typed context
once available, but should not invent a second exact-only clock.  Until that weld lands, committee
exact v4 remains fail-closed and v3 remains explicitly solo.
