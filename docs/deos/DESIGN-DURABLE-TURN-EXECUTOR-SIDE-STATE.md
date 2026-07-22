# Durable `TurnExecutor` side state

Status: receipt-head reconstruction and an exact-v3 composition fence are
implemented. The shared node-owned side-table migration below is the next
engine cut; it is not yet claimed live.

## Why this exists

The node deliberately constructs a fresh `TurnExecutor` for each submit,
verification, MCP, and finalized-block request. The ledger survives that
boundary, but an executor also contains mutable tables which affect admission
or committed roots. Replacing any of those tables with an empty constructor
default changes the transition function after every request.

`configure_turn_executor` now reconstructs two durable dimensions:

1. `note_nullifiers` from the faithful `(nullifier, value, append_seq)` table;
2. every agent's `last_receipt_hash` from the verified, interleaved durable
   receipt log.

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

The present head reconstruction is deliberately a correctness cut, not the
scaled endpoint: it revalidates and hashes the complete dense receipt log for
every fresh executor, `O(total receipt history)` per request. The next cut must
retain the already validated per-agent head index at append/recovery and seed
from that index in `O(number of agents)` (or retrieve the one required actor's
store-authenticated head in `O(1)`). Do not normalize a full-history walk as the
steady-state constructor.

## Inventory at HEAD

| Executor state | Consensus/admission effect | Current reconstruction |
| --- | --- | --- |
| `note_nullifiers` | local double-spend gate and nullifier root | durable faithful records |
| `last_receipt_hash` | agent causal admission | durable receipt log |
| `rate_limit_counters` | count-based epoch rate limits | **missing** |
| `rate_limit_sum_counters` | sum/window rate limits | **missing** |
| `bridged_nullifiers` | cross-federation replay gate | **missing** |
| `note_commitments` | duplicate-create gate and commitments root | **missing**; existing note table lacks value records |
| `note_revoked` | credential/channel revocation gate and root | **missing** |
| `reactive_registry` | promise/notify/react pending state | **missing** |
| `cell_migrations` | migration freeze and two-phase state | **missing** |
| `program_registry` | custom/sovereign verifier dispatch | node RAM has a registry, but fresh executors are not yet seeded from it and restart resets it |
| `factory_registry` | deployed factories and per-epoch budgets | **missing** |
| `revocation_channels` | fast channel-revocation view | **missing** |
| `per_cell_receipt_head` | touched-cell provenance chain | **missing**; receipt alone does not encode the write set |
| `pq_identity_registry` | host-anchored PQ admission | reconstructed from node-held identity state |
| exact FNSP-v3 admission token | one-shot proof authority | request-local by design |
| exact FNSP-v3 accumulator state | staged exact append state | durable exact store exists; live executor ownership is still WIP |

`last_write_set`, consumed-capability witnesses, universal-memory witnesses, and
yield buffers are per-execution outputs, not history tables. They should remain
request-local and be extracted before the executor is dropped.

There is also an atomicity defect before restart is considered:
`reactive_registry` and `factory_registry` can mutate before a later ledger
failure, but those mutations do not currently have complete inverse journal
entries. A long-lived shared handle must therefore stage these writes, not
merely make today's immediate mutations survive the next constructor.

## Next cut: one node-owned side-state handle

Do not add more per-ingress seed calls. Introduce one
`NodeExecutorConsensusState` owned by `NodeStateInner`, and give each fresh
executor shared handles to the same tables. The minimum first epoch is:

- rate-limit count and sum maps;
- bridged nullifiers;
- commitment and revocation accumulators;
- reactive registry and migration manager;
- factory epoch counters;
- deployed program-registry state;
- agent and per-cell receipt heads.

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

The commitment table needs an additive record before it can participate:
`(commitment32, value_u64, append_seq_u64)`. Revocation needs
`(domain_separated_key32, height_u64, append_seq_u64)`. Bridge, reactive,
migration, rate-limit, and factory state each need either a canonical delta in
the finalized commit or a proven derivation from an unpruned canonical turn
log. Depending on retained block bodies is not sufficient because commit-log
compaction must not erase consensus state.

## Promotion gate

Remove the exact-v3 single-effect fence only after a restart test performs this
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
