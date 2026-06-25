# Persistence & Recovery (`dregg-persist`)

The node's ONE durable store. Backed by `redb` — an embedded ACID key-value
store with a write-ahead log: every durable write is a transaction that either
commits fully (fsync at the commit boundary) or does not appear at all
(`persist/src/lib.rs:1`, `persist/src/lib.rs:164`).

The crate stores the commit log + secondary index, ledger checkpoints, blocklace
blocks/meta, notes/nullifiers, attested roots, forever-digest sets, channel
rosters, and config blobs (`persist/src/lib.rs:3`). The entry point is
`PersistentStore`, opened over a file (`PersistentStore::open`,
`persist/src/lib.rs:176`) or in memory (`open_in_memory`, `persist/src/lib.rs:189`).
`open` creates all tables and runs one idempotent index-shape migration
(`persist/src/lib.rs:182`).

## The canonical ledger root

`canonical_ledger_root(ledger)` is the byte-pinned full-ledger commitment both
the node (attested-root convergence) and the single-image World (durable-reopen
convergence) check against (`persist/src/lib.rs:78`). It is
`BLAKE3-derive-key("dregg-ledger-root-v2")` over cells sorted by id,
length-prefixed, each leaf `BLAKE3(postcard(WHOLE cell))` — committing the whole
cell (key / token / capabilities / lifecycle / state), so two ledgers that
finalized the same turns but diverged in cell CONTENT produce DIFFERENT roots
(`persist/src/lib.rs:62`, `persist/src/lib.rs:78`). Byte-stability is
load-bearing; the construction is fixed without a domain bump
(`persist/src/lib.rs:74`).

## The commit log — the recovery spine

`commit_log` is the authoritative, append-only record of the turns THIS node has
applied, in tau-finalized order (`persist/src/commit_log.rs:17`). It exists to
fix a torn-state bug: previously the recovery anchor (`executed_up_to`) and the
ledger checkpoint were written by independent transactions at different cadences,
so a crash between them lost every finalized turn in the gap, and receipts were
never persisted at all (`persist/src/commit_log.rs:3`).

### `CommitRecord`

One durable record of a finalized turn, stored in `COMMIT_LOG` keyed by commit
ordinal — its dense, gap-free position in applied order (`persist/src/commit_log.rs:75`,
`persist/src/commit_log.rs:82`). Each record carries: `ordinal`, `height`,
`block_id`, `block_executed_up_to` (the blocklace high-water mark as of this
commit), `turn_hash`, `creator`, `receipt_hash`, `ledger_root` (the canonical
root AFTER this turn), and `touched_cells` (post-state snapshots of every cell
the turn created/mutated) (`persist/src/commit_log.rs:86`–`persist/src/commit_log.rs:111`).
Each record's own `ledger_root` makes the log self-checking at every ordinal —
this is what recovery exploits (`persist/src/commit_log.rs:106`).

### The one-transaction commit

`commit_finalized_turn(expected_ordinal, record)` writes — in ONE redb
transaction — the commit record, the durable cursor advance, and every index
entry (`persist/src/commit_log.rs:241`, `persist/src/commit_log.rs:314`–`persist/src/commit_log.rs:356`):

- receipt-by-hash (`IDX_RECEIPT_BY_HASH`),
- turn-by-hash (`IDX_TURN_BY_HASH`),
- turn-by-`(height, creator, ordinal)` (`IDX_TURN_BY_HEIGHT_CREATOR`; key is
  8-byte BE height ++ 32-byte creator ++ 8-byte BE ordinal so range scans are
  height-major and several route-level turns can share a `(height, creator)`
  pair — `persist/src/commit_log.rs:123`),
- cell-by-id last-writer-wins snapshots (`IDX_CELL_BY_ID`).

The cursor is advanced LAST inside the same transaction (`persist/src/commit_log.rs:355`).
Writing at `expected_ordinal != cursor` is rejected: a lower ordinal is an
idempotent replay accepted only if the stored `turn_hash` matches (else an
integrity error); a higher ordinal is refused as a gap (the torn-state guard)
(`persist/src/commit_log.rs:275`–`persist/src/commit_log.rs:303`).

`commit_finalized_turn_with_burns` is the same, plus forever-digest burns
`(namespace, scope, digest)` written in the SAME transaction — the
same-transaction burn weld: a turn that burns an anti-replay digest lands its
record AND its digest atomically (`persist/src/commit_log.rs:260`,
`persist/src/commit_log.rs:344`).

### Crash-consistency invariants

Because all of the above land in one ACID transaction, these hold across an
arbitrary crash (`persist/src/commit_log.rs:29`):

- **No torn state.** `commit_cursor() == commit_log_len() + commit_compacted_floor()`;
  every ordinal in `[compacted_floor, cursor)` resolves to a record
  (`persist/src/commit_log.rs:32`, `persist/src/commit_log.rs:198`).
- **No lost finalized turn.** A durably-committed turn is recoverable with full
  coordinates and post-state, either from its record or from a checkpoint that
  subsumes it (`persist/src/commit_log.rs:37`).
- **No double-apply.** Recovery resumes from `commit_cursor()`; a turn whose
  transaction did not commit is idempotently re-applied, one that did is never
  re-applied (`persist/src/commit_log.rs:43`).
- **Index agrees with the log.** Every index entry exists iff the log has the
  record (`persist/src/commit_log.rs:51`).

### Recovery anchors (read-side)

- `commit_cursor()` — the crash-consistent recovery anchor (the count of applied
  turns), read inside the commit transaction so it can never be torn against the
  record it counts (`persist/src/commit_log.rs:184`).
- `recovered_block_cursor()` — the `block_executed_up_to` of the last committed
  turn; resume blocklace processing here. Written in the same transaction as its
  turn, so it can never run ahead of the durable ledger
  (`persist/src/commit_log.rs:439`).
- `recovered_ledger_root()` — the durable post-state root the node converged to
  (the last record's `ledger_root`); a recovered node MUST reproduce it
  (`persist/src/commit_log.rs:461`).
- `cell_overlay_since(checkpoint_height)` — the last-writer-wins overlay of cell
  post-states committed after a checkpoint; re-derived from the log (not the
  rebuildable index) so recovery never trusts the index for correctness
  (`persist/src/commit_log.rs:478`).

### Index verify + rebuild

`verify_index_agrees_with_log()` walks the log forward (every record's hash
entries resolve to its ordinal) and each index backward (no orphans), and checks
the cell index equals the log's last-writer-wins projection, returning an
`IndexAuditReport` (`persist/src/commit_log.rs:615`, `persist/src/commit_log.rs:138`).
`report.ok()` requires the compaction-aware density invariant
`cursor == records + compacted` plus zero missing/orphan/mismatched entries
(`persist/src/commit_log.rs:165`). `rebuild_index_from_log()` clears every index
table and replays the log in one transaction — the log is the source of truth;
the cursor is left untouched (`persist/src/commit_log.rs:748`). The one-time
`migrate_height_creator_index` (run from `open`) detects legacy 40-byte
`(height, creator)` keys and rebuilds from the log (`persist/src/commit_log.rs:1230`).

## `recover_to_last_consistent` — recover a torn/divergent image

`recover_to_last_consistent()` salvages a torn or poisoned image instead of
refusing it (`persist/src/commit_log.rs:1064`). The boot convergence check
reconstructs `checkpoint ⊕ overlay` and asserts the canonical root equals
`recovered_ledger_root()`; a torn write (process killed between the input-turn
config write and the commit-record txn, a genesis-path mutation over a
turn-touched cell, a second writer tearing the file) leaves the tail inconsistent
and would strand the owner (`persist/src/commit_log.rs:1020`).

Because each record carries its OWN post-state root, the log is self-checking at
every ordinal. The function reconstructs `checkpoint ⊕ overlay[..=k]` with the
SAME `canonical_ledger_root` the records were written under, walking the live log
in ordinal order, applying each record's `touched_cells` last-writer-wins, and
remembering the last ordinal whose running root matches its recorded `ledger_root`
(`persist/src/commit_log.rs:1044`, `persist/src/commit_log.rs:1083`–`persist/src/commit_log.rs:1107`).
It then TRUNCATES the divergent tail `(last_good+1, cursor)` in ONE transaction —
removing doomed records and their receipt/turn/`(h,c)` index entries, re-deriving
the cell index from survivors, and REGRESSING the cursor to `last_good+1` (a
truncated turn was never safely applied) (`persist/src/commit_log.rs:1127`–`persist/src/commit_log.rs:1210`).

Edge cases: an already-consistent head is left untouched (returns 0)
(`persist/src/commit_log.rs:1122`); if NOTHING converges it returns an integrity
error rather than silently emptying the log (`persist/src/commit_log.rs:1114`).
A crash mid-truncation leaves the pre-recovery store in place, so recovery is
itself idempotent and crash-safe (`persist/src/commit_log.rs:1055`).

## Compaction — bounding the WAL

`compact_below(height)` removes the contiguous ordinal prefix of records strictly
below `height`, but ONLY when a covering ledger checkpoint at/above `height`
subsumes their finalized state; otherwise it is a no-op returning 0 (the safety
guard against losing a finalized turn) (`persist/src/commit_log.rs:871`,
`persist/src/commit_log.rs:880`). It preserves the cursor (only the physical
record count drops), advances `commit_compacted_floor` by exactly the count
removed, retains each compacted turn's `block_id` in `COMMIT_COMPACTED_BLOCK_IDS`
(reported by `commit_log_block_ids` so the identity execution cursor never
re-applies it), and re-derives the cell index from survivors — all in one
transaction (`persist/src/commit_log.rs:849`–`persist/src/commit_log.rs:998`).
Checkpointing co-drives compaction: `checkpoint_ledger` writes the checkpoint
FIRST (the load-bearing durability) then drives `compact_below`; a compaction
error is logged but does not fail the checkpoint (`persist/src/ledger_store.rs:60`).

## Ledger checkpoints

`LedgerCheckpoint` is the serializable full-ledger snapshot (height + all cells +
sovereign commitments/registrations), since `Ledger` holds non-serializable
runtime state (channels, cached Merkle tree) (`persist/src/ledger_store.rs:34`,
`persist/src/ledger_store.rs:38`). `checkpoint_ledger(ledger, height)` persists it
keyed by height and updates the latest-height metadata
(`persist/src/ledger_store.rs:72`); `load_latest_ledger_checkpoint`,
`latest_ledger_checkpoint_height`, `prune_ledger_checkpoints(keep_last_n)` round
it out (`persist/src/ledger_store.rs:118`, `persist/src/ledger_store.rs:181`,
`persist/src/ledger_store.rs:255`). The ledger is derived state (reconstructible
from the blocklace); checkpoints exist for fast startup without full replay
(`persist/src/ledger_store.rs:3`).

## Forever digests — restart-durable anti-replay

A forever digest is one the protocol burns exactly once and refuses forever (a
trustline draw, a court resolved-evidence digest)
(`persist/src/forever_digests.rs:1`). The node keeps these in memory for the hot
refusal path; this module is the durable backing — written in one WAL-backed redb
transaction (fsync before the in-memory insert is acknowledged) and reloaded at
boot (`persist/src/forever_digests.rs:8`). Keys are the 65-byte composite
`namespace ++ scope ++ digest` (`persist/src/forever_digests.rs:24`); writes are
append-only (digests are never removed) (`persist/src/forever_digests.rs:13`).
`record_forever_digest` is idempotent (`persist/src/forever_digests.rs:39`).
`forever_key` is `pub(crate)` so the commit log can burn digests in the same
transaction as a turn's record (`persist/src/forever_digests.rs:21`).

## Tables

All tables are `redb::TableDefinition`s in `persist/src/tables.rs`: the commit
log `COMMIT_LOG` (`persist/src/tables.rs:142`); the four index tables
`IDX_RECEIPT_BY_HASH` / `IDX_TURN_BY_HASH` / `IDX_TURN_BY_HEIGHT_CREATOR` /
`IDX_CELL_BY_ID` (`persist/src/tables.rs:149`–`persist/src/tables.rs:179`);
`COMMIT_COMPACTED_BLOCK_IDS` (`persist/src/tables.rs:216`); `LEDGER_CHECKPOINTS`
(`persist/src/tables.rs:75`); `FOREVER_DIGESTS` (`persist/src/tables.rs:240`);
plus blocklace, notes/nullifiers, attested roots, rosters, and metadata tables.
The cursor and compaction floor are metadata keys `META_COMMIT_CURSOR` and
`META_COMMIT_COMPACTED` (`persist/src/tables.rs:186`, `persist/src/tables.rs:199`).

## How boot recovery composes (caller: starbridge-v2)

`PersistentImage::recover` runs the same checkpoint-load → overlay → fail-closed
convergence the node does (`starbridge-v2/src/persistence.rs:341`):

1. load the latest full ledger checkpoint, or empty (`starbridge-v2/src/persistence.rs:343`);
2. apply `cell_overlay_since(checkpoint_height)` last-writer-wins — the
   `recover = checkpoint ⊕ overlay` half (`starbridge-v2/src/persistence.rs:351`);
3. FAIL-CLOSED: the reconstructed `canonical_ledger_root` MUST equal
   `recovered_ledger_root()`, else `OpenError::Divergent { got, expected }`
   (`starbridge-v2/src/persistence.rs:356`);
4. load durable genesis cells + committed turns up to `commit_cursor()` to rebuild
   the in-RAM spine (`starbridge-v2/src/persistence.rs:369`).

`recover_to_last_consistent` is the escape hatch when step 3 would otherwise
strand the owner; it is also exposed on the image
(`starbridge-v2/src/persistence.rs:249`).

## Lean grounding (`Dregg2.Distributed.CrashRecovery`)

The `recover = checkpoint ⊕ overlay` model is verified in
`metatheory/Dregg2/Distributed/CrashRecovery.lean`:

- `recover` is defined as `applyWrites checkpoint overlay`
  (`CrashRecovery.recover`, line 149).
- `recover_eq_replay`: `recover genesis log k = replay genesis log` for any cut
  `k` — the checkpoint-cut is invisible; recovery yields the full-replay ledger
  (`CrashRecovery.recover_eq_replay`, line 193).
- `recover_independent_of_checkpoint`: two nodes that checkpointed at different
  cuts recover the byte-identical ledger (`CrashRecovery.recover_independent_of_checkpoint`,
  line 204).
- `recover_full_checkpoint`: an all-checkpointed node recovers from the checkpoint
  alone (`CrashRecovery.recover_full_checkpoint`, line 211).

All four rest only on `{propext, Classical.choice, Quot.sound}`, asserted via
`#assert_axioms` (`CrashRecovery.lean:220`–`225`). The doc-comment notes the
`ledger_root` equality the node checks is `recover_eq_replay` instantiated at the
canonical-root map (`CrashRecovery.lean:61`), and that the theorem is non-vacuous
(persisting the full post-checkpoint log is load-bearing; `CrashRecovery.lean:44`).
