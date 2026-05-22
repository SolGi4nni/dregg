# Turn Execution Model

## 1. What IS a Turn?

A Turn is the atomic unit of state transition. Data structure (`turn/src/turn.rs`):

```
Turn { agent: CellId, nonce: u64, call_forest: CallForest, fee: u64,
       memo?, valid_until?, previous_receipt_hash?, depends_on: Vec<[u8;32]> }
```

The call forest is a tree of `Action` nodes, each targeting a cell with effects (SetField, Transfer, GrantCapability, NoteSpend/NoteCreate, BridgeMint, etc.), authorization (Ed25519 signature, ZK proof, breadstuff token, or None), preconditions, and a delegation mode for children.

**Key difference from Ethereum**: Turns are call *forests* (multiple roots), not single calls. Authorization is per-action-node, not per-transaction. Mina-style balance_change with excess tracking replaces explicit paired transfers -- excess must net to zero across the entire turn.

**Key difference from Mina**: Cells replace accounts. Capability-based access (c-list) replaces token approvals. Federated consensus replaces global L1. Computron metering replaces block gas limits.

## 2. Where Do Turns Execute Today?

**Both locally and on federation nodes.** The same `TurnExecutor` struct runs in both contexts.

**SDK local execution** (`sdk/src/runtime.rs`): `AgentRuntime` holds a local `Ledger` + `TurnExecutor`. The agent constructs turns and executes them against their local ledger replica. This gives instant feedback, receipt generation, and IVC state updates. The local ledger is initialized with the agent's own cell.

**Federation node execution** (`turn/src/executor.rs`): Nodes run the same `TurnExecutor::execute()` against the canonical ledger. The executor checks nonces, fees, preconditions, authorization (sig/proof), applies effects depth-first through the call forest, meters computrons, and either commits (producing a `TurnReceipt` with pre/post state hashes) or rolls back atomically via journal replay.

**Wire layer** (`wire/src/server.rs`): The SiloServer handles proof *presentation* (verifying STARK proofs against the federation root), not direct turn submission. Turn submission flows through the federation consensus layer.

**There is no semantic difference** between local and federated execution -- same code path, same rules. The difference is *authority*: only federation-executed turns update the canonical state and produce receipts signed by the executor.

## 3. Can Turns Be Fully Off-Chain?

**Partially.** Two parties can execute turns locally against shared state and exchange receipts. But they lose:

- **Double-spend protection**: The federation's nullifier set and nonce tracking are the canonical double-spend barriers. Without federation ordering, Alice can sign contradictory turns to Bob and Carol.
- **Ordering guarantees**: Causal chaining (`coord/src/causal.rs`) gives happened-before within a single party's history, but cannot prevent forks without a finality source.
- **Revocation freshness**: Capability revocations propagate through the federation. Off-chain parties see stale revocation state (bounded by `max_staleness` in SnapshotRefresh delegation).

The federation provides: ordering, canonical state, double-spend finality, and revocation propagation. Skip it and you get optimistic local execution with deferred settlement.

## 4. Optimistic Execution and the Fast Path

**Yes, the code explicitly supports this.** `turn/src/fast_path.rs` implements LUTRIS-style consensusless finality:

- A turn qualifies if ALL write-set cells are owned solely by the signer and `depends_on` is empty.
- Protocol: client broadcasts signed turn -> 2f+1 validators each check (sig, nonce, fee, ownership) and acquire a `CellLockEntry` -> client assembles a `TurnCertificate` from the lock acknowledgements -> certificate is presented for execution.
- Finality in 2 network round trips, no BFT consensus needed.
- Safety: at most one turn per (cell, nonce) can collect a quorum (any two quorums overlap). Locks expire after `lock_timeout_blocks` (default 30).

**Journal supports speculation**: The `LedgerJournal` records every mutation's prior value. On failure, `journal.rollback(ledger)` replays entries in reverse. Zero-cost on success (journal is dropped). This enables speculative execution with cheap undo.

**State channel pattern**: Not explicitly implemented, but the building blocks exist -- `previous_receipt_hash` chains receipts causally, `CommitmentMode::Partial` lets parties sign their fragment independently, and the journal enables local speculative execution. Settlement would require submitting the final receipt to the federation.

## 5. Turn Composition and Batching

**Multi-party composition** (`turn/src/composer.rs`): `TurnComposer` assembles `SignedFragment`s (each using `CommitmentMode::Partial`) into one atomic `Turn`. Each signer commits only to their action + position + federation_id + nonce -- they don't see other fragments. Enables atomic swaps and DEX fills.

**Pipelined execution** (`turn/src/eventual.rs`): `Pipeline`/`TurnBatch` declares dependency edges between turns. Turns are topologically sorted and executed in causal order. `EventualRef` references resolve to outputs of earlier turns in the batch. Supports `federation_id` for cross-federation references.

**Causal ordering** (`coord/src/causal.rs`): `CausalTurn` wraps a turn with hash-pointers to causally-prior turns, forming a DAG. `previous_receipt_hash` on the Turn itself provides the same chaining at the protocol level.

## 6. Semi-Trustful Execution

**Fast path = peer-to-peer for owned cells**: If all write-set cells belong to the signer, validators just check/lock without consensus. This is the "trust-lite" path -- no BFT needed, just quorum acknowledgement.

**Must go through federation when**:
- Turn writes to cells owned by different parties (cross-cell targeting)
- Turn has `depends_on` (conditional on other turns)
- Privacy notes are spent/created (nullifier set is global)
- Bridge operations (require trusted roots from federation)

**SnapshotRefresh delegation**: A child cell inherits its parent's c-list as a frozen snapshot. The child can act offline using the snapshot. Revocation is eventual -- the parent bumps its `delegation_epoch` and the child's snapshot becomes stale after `max_staleness`. This is the explicit "semi-trustful offline operation" mechanism.

## 7. Comparison to Other Models

| | Pyana | Rollups | State Channels | Anoma |
|---|---|---|---|---|
| Execution location | Federation nodes (canonical) + local (optimistic) | Off-chain sequencer | Off-chain between parties | Solver network |
| Settlement | Federation consensus (BFT) or fast-path (quorum locks) | L1 validity/fraud proof | L1 dispute resolution | L1 settlement |
| Off-chain pattern | Fast path (owned cells, 2 RTT), SnapshotRefresh delegation | All execution off-chain | Full channel lifecycle | Intent matching off-chain |
| Dispute model | None needed -- fast path has quorum safety, consensus path has BFT finality | Fraud proof (optimistic) or validity proof (ZK) | On-chain dispute with state submission | None -- validity proofs |
| Composability | Call forest with partial commitment; TurnComposer for multi-party | Limited cross-rollup | Only between channel parties | Intent solver composes |

The closest analog is **Sui's owned-object fast path** (same LUTRIS lineage): single-owner objects skip consensus entirely. Pyana generalizes this to cells with the same ownership check. Multi-owner transitions require the consensus path, analogous to Sui's shared-object path through Narwhal/Bullshark.
