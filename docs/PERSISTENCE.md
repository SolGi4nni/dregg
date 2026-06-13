# PERSISTENCE — what survives a restart, and why

*(the unified node-durability story; companion to `docs/ORGANS.md`'s
parameterization discipline and the commit-log crash-consistency design in
`persist/src/commit_log.rs`. Lean twins:
`metatheory/Dregg2/Distributed/CrashRecovery.lean`,
`Distributed/CatchupConverges.lean`, `Distributed/CheckpointPrune.lean`,
`Apps/Trustline.lean` §10b.)*

## 1. The one substrate

The node has exactly one durable store: `dregg-persist`, a redb (embedded
ACID, WAL-backed) database at `<data_dir>/dregg.redb`, opened once in
`node/src/state.rs` and shared by every subsystem. Every durable write is a
redb transaction: it either commits fully (fsync at the commit boundary) or
does not appear at all. There is no second journal, no sidecar files except
the node key and `known_federations/`.

Its load-bearing core:

* **The commit log + index** (`persist/src/commit_log.rs`): the append-only
  record of every finalized turn this node applied, written in ONE
  transaction with the commit cursor, the secondary indexes, and the touched
  cells' post-states. Recovery = checkpoint ⊕ overlay; the Lean theorem
  `recover_eq_replay` (CrashRecovery.lean) proves this equals full replay,
  for any checkpoint cut, with a NEG witness that dropping a record changes
  the state.
* **Ledger checkpoints** (`ledger_store.rs`) and **blocklace blocks + meta**
  (`blocklace_store.rs`): the consensus substrate's durable half, pruned
  under `CheckpointPrune.lean`'s safety law.
* **Notes/nullifiers, witnessed receipts, attested roots, proof hashes,
  config blobs**: per-collection tables, all in the same store.
* **Forever-digest sets** (`forever_digests.rs`): the restart-durable
  anti-replay carriers — see §3.

Verdict on the crate: **keep and extend**. The commit-log core is current and
is the node's recovery spine. Four modules were dregg1-era residue with zero
consumers outside the crate's own tests — `tokens.rs` (TokenChain/fold
steps), `recovery.rs` (`recover_federation_state`), `keys.rs` (encrypted
signing keys; the node keeps its key in `node.key`), and `audit.rs` (the
standalone audit log) — and have been **retired** under the cutover-ledger
discipline (verified zero external consumers by grep at deletion time; their
tables are no longer created, and a pre-existing table in an old store file is
simply ignored by redb). The checkpoint pruner no longer touches an audit log.

## 2. The axis (the parameterization discipline, applied)

Persistence is a per-collection axis (ORGANS header): every node-held
collection sits at a declared point, and the point is the design — not an
accident of which HashMap someone reached for.

* **`attested`** — inside the receipt discipline: recorded permanently;
  conservation-grade; the derivability invariant applies. Deletion is not a
  legal write.
* **`retained(window)`** — attested for a challenge period, then prunable;
  the temporal algebra prices the window.
* **`prunable`** — deletion is a guarded write: who may remove is law.

Orthogonal to the axis is **derivability**: whether the collection can be
rebuilt from the cells (the cell is the truth) or is genuinely node-local.
A derived collection may legitimately sit at `prunable` — losing it loses
nothing. A node-local-but-load-bearing collection at `prunable` is a bug
wearing an architecture costume.

## 3. The census (every node-held registry, with its assignment)

### Derived from cells — rebuild is CORRECT; in-memory is the right home

| Collection | Where | Truth |
|---|---|---|
| Budget coordinators (Stingray shadows) | `state.rs::budget_coordinators` | the trustline cell's registers; `ensure_coordinator` rebuilds `balance = line − settled`, re-debits `drawn − settled` (Lean `epochSlice`, `derived_view_faithful`) |
| Channel rosters | `channels_service.rs::Room.roster` | the cell's `member_root` commitment; the node-held roster must RE-COMMIT to it (`RosterStale` refuses otherwise) — but see the caveat below |
| Court bond registry + bond-cell bindings | `equivocation_court_service.rs::CourtLedger.{registry,bond_cells}` | the bond cells on the live ledger (deterministic ids: `bond_cell_id(operator_pk, strand)`); an unrestored bond fails CLOSED (`NothingAtStake`, no value moves) |
| Program registry, routing table, lock table | `state.rs` | re-derivable / session-scoped |

These are `prunable` by construction: the restart IS the prune, and the
rebuild rule is proven faithful (trustlines) or fail-closed (court bonds).

**The roster caveat (named; the durable carrier landed):** the cell holds
only the roster's *commitment*, not its content. The node-held member→seal-pk
map (and the epoch anchor) are verifiable against the cell but not derivable
from it. The durable carrier is now in place: the `channel_rosters` table
(`persist/src/channel_rosters.rs`, cell id → postcard `(anchor, members)`)
is written in ONE committed transaction after every committed epoch step
(open/join/remove/rekey — `channels_service::persist_roster`) and reloaded at
boot (`ChannelRegistry::restore_rosters`), where each stored roster is
**re-committed** against the recovered ledger's on-cell `member_root` before
the room is rebuilt: a roster whose `roster_root` ≠ the cell's `member_root`
(or whose cell is gone / not a channel cell) is discarded *and* durably
removed, so a restart no longer serves `RosterStale` for a roster that still
matches its cell, and a post-restart `RosterStale` means genuine divergence,
never a mere restart. Epoch keys are node-minted secrets that are NOT
persisted (a delivery property, not a soundness one — see §3 cache); a
restored room rekeys to re-establish forward delivery, while membership
operations and the SSE relay resume immediately. The roster bytes are stored
opaquely (the node owns the `Roster` type via `dregg_sdk::channels`), keeping
`dregg-persist` independent of the SDK.

### Node-local AND load-bearing — must be durable (`attested`)

These sets are **not derivable from the cells**, and forgetting them turns a
refusal into an acceptance (fail-open):

1. **Trustline forever digests** (`TrustlineRegistry`): committed draw
   digests, shadow-rebuild digests, settle-unapplied compensation digests.
   The cell carries only the LAST digest (`TL_DIGEST_SLOT`); the Stingray
   slice's `debits` list resets every rebalance epoch. The Lean forever-laws
   (`no_double_draw_forever`, `draw_replay_refused_across_epochs`) quantify
   over the whole history — the registry is their deployed carrier, so the
   carrier must outlive the process.
2. **Court resolved-evidence digests** (`CourtLedger`): the
   no-double-resolve set. A forgotten verdict re-admits the same exhibit
   against a re-posted bond — a double-slash.

**The mechanism** (`persist/src/forever_digests.rs`): one redb table
(`forever_digests`), key = `namespace ++ scope ++ digest` (1+32+32 bytes),
append-only. The digest is written durably (one committed transaction)
**before** the in-memory insert is acknowledged
(`trustline_service::record_digest_durable`, `execute_slash` step 6); both
sets are reloaded at boot (`TrustlineRegistry::load`, `CourtLedger::load`).
A durable-write failure after a committed turn cannot unwind the turn, so it
degrades — loudly, `tracing::error!` — to live-process-only refusal; an
unreadable table at boot likewise names the narrowing instead of papering it.
Restart-shaped tests pin the property end to end
(`draw_digest_refused_across_restart`,
`resolved_evidence_refused_across_restart`, plus the persist-level reopen
test).

Why not always a row in the commit log? The burn is *caused* by a committed
turn but is not always a turn artifact: rebuild digests and court verdicts
burn outside any single turn's receipt, and the refusal lookup is a point
query, not a replay. The forever table rides the same store (same WAL, same
fsync discipline) without bending the log's "one record per applied turn"
invariant.

**The same-transaction burn weld** (`commit_finalized_turn_with_burns`,
`persist/src/commit_log.rs`): for a burn that *is* an artifact of a turn this
node finalizes itself — an **in-turn** site — the digest can land in the SAME
redb transaction as that turn's `CommitRecord`. After an arbitrary crash,
either both are durable or neither is: no crash can leave the turn durable
without its burn, or the burn durable without its turn (the welded test
`burns_land_atomically_with_the_commit_record` pins exactly this, with the
idempotent-replay no-op). The commit-log index key gained a trailing ordinal
(`(height, creator, ordinal)`) so several route-level turns can share a
`(height, creator)` pair without colliding; a one-time boot migration
(`migrate_height_creator_index`) rebuilds an old 40-byte index from the log.

For an **out-of-turn** burn — the trustline draw/settle digests and court
verdicts as the routes finalize them today — the carrier is **journal-first**:
the digest is written durably (one committed transaction) *before* the
in-memory insert is acknowledged (`record_digest_durable`, `execute_slash`
step 6), and reloaded at boot. These route paths mutate the live ledger and
burn the digest as separate committed transactions (the finalized
`CommitRecord` for the route turn is written later, on the consensus path in
`blocklace_sync`), so the burn is durable independent of — and ordered
before — the acknowledgement. The remaining crash window is post-burn,
pre-ack: a crash there loses nothing of the burn (it committed first); a crash
*before* the burn loses a turn whose response was never delivered, and the
client safely retries against a fresh digest. A durable-burn failure after the
ledger moved cannot unwind the move, so it degrades — loudly, `tracing::error!`
— to live-process-only refusal; an unreadable table at boot likewise names the
narrowing instead of papering it.

### Cache — `prunable`/`retained(window)`, loss is priced

| Collection | Point | Notes |
|---|---|---|
| Channel ciphertext ring (`Room.ring`) | `retained(window)` | the node relays what it cannot read; the ring is a bounded delivery buffer, the SSE cursor's source. Restart loses undelivered ciphertext — a delivery property, not a soundness one. A durable ring is a service-quality lane, not a refusal lane. |
| Event log ring, witnessed-receipt order, proof-pending set | `prunable` / already persisted | bounded UX surfaces |
| Epoch keys the node minted (`Room`) | `prunable` | re-keying mints fresh ones; the cell pins the commitment |

## 4. What the Lean models — and what it does not

**Modeled** (axiom-clean, differential-pinned):

* **Commit-log recovery**: `CrashRecovery.lean` — recover = replay, cut
  independence, NEG witness. The model is the *cell map*; it is parametric
  in the cell's value.
* **Catch-up**: `CatchupConverges.lean` (#73) — out-of-order, buffered
  reception converges to the leader's finalized state.
* **Prune safety**: `CheckpointPrune.lean` — pruning below a checkpoint
  preserves recoverability.
* **The forever-laws themselves**: `Apps/Trustline.lean`
  (`no_double_draw_forever`, `draw_replay_refused_across_epochs`, the §10b
  `ensure_coordinator` rebuild faithfulness), `federation/src/court.rs`'s
  no-double-resolve (Lean-shaped in `Proof/BFT.lean`'s equivocation models).

**Not modeled** (the honest gap this design closes in Rust, named for the
metatheory lane):

* The Lean forever-laws quantify over one unbroken state history; **process
  death is not an event in any Lean schedule**. `CrashRecovery.lean` models
  crash-recovery for the *ledger map only* — `CommitRecord.touched_cells`
  carries no registry, so the recovered state in the model simply has no
  digest sets to lose. There is no theorem of the shape "registry ⊇ all
  burned digests across a crash cut". The natural statement is a small
  extension of CrashRecovery's log: records carry `(writes, burns)`, recovery
  folds both, and `draw_replay_refused` lifts across the cut. That is the
  metatheory closure lane for this design (read-only observation here; the
  Rust side now satisfies the intended semantics).
* The channel roster's availability-after-restart (the §3 caveat) has no
  Lean counterpart; `ChannelGroup.lean` models the cell program's epoch/root
  laws, with the roster content explicitly off-cell.
