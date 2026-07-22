# Durable `TurnExecutor` side state

Status: the finalized-turn store has one atomic executor-consensus-state bundle
for accumulator records, sparse rate/factory snapshots, and exact reactive
registry/nullifier CAS images. Fresh executors fail-closed while restoring those
images. The live exact-FNSP-v3 finality route carries the bundle in the same
transaction as its activation, exact state append, signed frame, full receipt,
faithful root, spend records, and commit cursor. The ordinary finalized-turn
route now captures and commits the same complete bundle. Both routes resolve
promises on the retained isolated executor, atomically persist the exact typed
resolution batch with the source commit, and publish only after a `Fresh`
outcome. The superseded `NodeState` pending-registry mirror is deleted.

## Why this exists

The node deliberately constructs a fresh `TurnExecutor` for each submit,
verification, MCP, and finalized-block request. The ledger survives that
boundary, but an executor also contains mutable tables which affect admission
or committed roots. Replacing any of those tables with an empty constructor
default changes the transition function after every request.

`configure_turn_executor` reconstructs these durable dimensions before an
executor may admit a turn:

1. `note_nullifiers` from the faithful `(nullifier, value, append_seq)` table;
2. every agent's `last_receipt_hash` from the verified, interleaved durable
   receipt log;
3. note-commitment, revocation, and bridged-nullifier accumulators;
4. count and sum rate-limit frontiers;
5. the factory registry and its epoch budgets;
6. the pending-turn registry and the dedicated React replay set.

The receipt reconstruction validates the entire per-agent causal chain before
seeding any head. A corrupt suffix therefore cannot produce a partially seeded
executor. The exact FNSP-v3 route is also fenced to one semantic `NoteSpend`:
game rewards, bridge effects, or other consequences must be separately
finalized outbox turns until the remaining side state has one durable owner.
The superseded ingress `seed_executor_receipt_head` helper and all of its call
sites are deleted. A request- or handler-supplied predecessor therefore has no
write path into executor authority; `TurnExecutor` compares the signed turn
directly with the store-authenticated map.
The strict exact route is also forced onto the Rust producer for this staging
epoch: the Lean producer does not yet project the exact FNS3, commitment, or
revocation side accumulators, so treating this route as root-agreeing would drop
consensus state from the authored commitment.

The exact epoch maintains a transactionally updated per-agent receipt-head
index and fully rebuilds it during recovery. Some ordinary constructor paths
still revalidate the dense receipt log. That correctness-first walk is not the
scaled endpoint: all executor construction should consume the already audited
head index, with a single actor lookup in `O(log agents)` or better.

## Inventory at HEAD

| Executor state | Consensus/admission effect | Current reconstruction |
| --- | --- | --- |
| `note_nullifiers` | local double-spend gate and nullifier root | durable faithful records |
| `last_receipt_hash` | agent causal admission | durable receipt log |
| `rate_limit_counters` | count-based epoch rate limits | transactional canonical snapshot; atomic store/reseed implemented |
| `rate_limit_sum_counters` | sum/window rate limits | transactional full-width `u64` canonical snapshot; atomic store/reseed implemented |
| `bridged_nullifiers` | cross-federation replay gate | typed durable set + frontier; atomic store/reseed implemented |
| `note_commitments` | duplicate-create gate and commitments root | durable `(commitment, value, append_seq)` records + frontier; atomic store/reseed implemented |
| `note_revoked` | credential/channel revocation gate and root | durable `(key, height, append_seq)` records + frontier; atomic store/reseed implemented |
| `reactive_registry` | promise/notify/react pending state | canonical whole-image CAS; atomic store/reseed implemented on exact and ordinary finality; typed durable resolution outbox has cursor HTTP + WebSocket surfaces |
| `reactive_nullifiers` | React one-shot replay gate | dedicated domain, canonical set CAS; atomic store/reseed implemented |
| `cell_migrations` | migration freeze and two-phase state | **missing** |
| `program_registry` | custom/sovereign verifier dispatch | durable local-admin registry with write-before-publish and fail-closed restore; federation-consensus deployment receipt is still missing |
| `factory_registry` | deployed factories and per-epoch budgets | canonical snapshot/inverse; atomic store/reseed implemented |
| `revocation_channels` | fast channel-revocation view | **missing** |
| `per_cell_receipt_head` | touched-cell provenance chain | durable current+compacted-baseline maps, removal provenance, rebuild/audit, and startup restore implemented; sovereign/mixed commits with distinct receipts need a richer commit schema |
| `pq_identity_registry` | host-anchored PQ admission | reconstructed from node-held identity state |
| exact FNSP-v3 admission token | one-shot proof authority | request-local by design |
| exact FNSP-v3 accumulator/frame state | exact spend and receipt-chain authority | live finality route atomically activates and advances the exact state/frame with faithful and executor state; current route is one strict spend in solo devnet policy |

`last_write_set`, consumed-capability witnesses, universal-memory witnesses, and
yield buffers are per-execution outputs, not history tables. They should remain
request-local and be extracted before the executor is dropped.

Rate accounting no longer has this pre-restart defect. One execution owns a
staged rate state: each action observes earlier accepted debits in the same
forest, while the stage is published only after the entire turn and optional
Lean veto have accepted. Rejection at any later action therefore leaves both
count and sum maps unchanged. `CellProgram::Cases` contributes the matched
branch constraints, multiple simultaneously active scalar rate constraints
fail closed instead of silently selecting one, and sum history remains `u64`
end-to-end rather than truncating through the predicate evaluator's old `u32`
lane.

`factory_registry` mutations have selective inverses and `reactive_registry`
mutations have a complete journal plus durable predecessor/successor CAS. A
candidate executor remains isolated until the carrying redb transaction returns
fresh success. Resolution events stay candidate-local until that point;
`ReadyToExecute` is notification-only because it contains an unsigned turn.

## Remaining cuts

Do not add per-ingress seed calls or a second mutable RAM owner. The durable
snapshot/CAS bundle is the owner; a request gets an isolated executor image,
and only a fresh atomic commit may publish its successor. The remaining engine
work is:

- persist migration and channel-revocation authority under the same commit;
- make custom-program deployment a federation-consensus operation rather than
  a local administrative write;
- represent sovereign/mixed per-cell receipt provenance without collapsing
  distinct receipts into `CommitRecord::receipt_hash`;
- consume the node's typed, replay-idempotent promise-resolution cursor in the
  Discord, Telegram, and game-web adapters (the durable HTTP/WebSocket node
  surface is implemented; adapter presentation remains);
- switch all ordinary receipt-head construction to the audited online index.

The handle must satisfy these rules:

1. **One mutation window.** Side-table changes and ledger changes are staged
   together; rejection rolls both back.
2. **Commit last.** A finalized turn writes the ledger overlay, receipt,
   append-only accumulator records, side-state delta, and commit cursor in one
   durable transaction before publishing the new in-memory state.
3. **Exact replay.** Restart reconstructs full records, including values and
   append sequence. A presence-only commitment or revocation row is
   insufficient for the circuit-faithful root and must fail closed.
4. **One ingress.** HTTP, signed turn, MCP, local host, and block finalization
   all obtain executors through the same constructor and commit/extract path.
5. **Typed version.** The durable side-state delta has a fixed version and
   canonical record schema. Unknown versions, gaps, duplicate sequence numbers,
   or cursor disagreement are integrity errors, never empty defaults.

Accumulator and policy state use typed canonical records or snapshots, never a
derivation from prunable block bodies. Compaction folds per-cell provenance into
an authenticated baseline and rebuilds live suffixes over it. The same rule
applies to the remaining migration/channel state: compaction must preserve its
complete admission frontier.

## Promotion gate

Broaden the exact-v3 strict-spend envelope only after a restart test performs this
sequence through distinct fresh executors:

1. create a note and reject its duplicate;
2. spend/bridge once and reject replay;
3. trip count and sum rate limits across request boundaries;
4. revoke a credential/channel and reject its later use;
5. promise then react exactly once;
6. begin a migration and observe the frozen cell;
7. execute an exact spend plus a separately finalized game consequence;
8. restart and repeat every hostile operation with the same refusal;
9. compare every reconstructed eight-felt root and receipt head with the
   pre-restart values.

Only then is multi-effect exact-v3 composition a protocol feature rather than a
fresh-executor assumption.
