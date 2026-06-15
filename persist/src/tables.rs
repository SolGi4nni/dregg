//! Table definitions for the redb database.
//!
//! Each table is defined as a constant with a fixed name and typed key/value pairs.
//! redb uses these definitions to enforce type safety at the database level.

use redb::TableDefinition;

/// Revocation set: token_id (string) -> revocation timestamp.
///
/// Key: token ID as a string (variable length).
/// Value: i64 timestamp when the revocation was recorded.
pub const REVOCATIONS: TableDefinition<&str, i64> = TableDefinition::new("revocations");

/// Attested roots: height (u64) -> serialized StoredAttestedRoot.
///
/// Key: block height (monotonically increasing).
/// Value: postcard-serialized `StoredAttestedRoot` struct.
pub const ATTESTED_ROOTS: TableDefinition<u64, &[u8]> = TableDefinition::new("attested_roots");

/// Metadata table for store-level counters and configuration.
///
/// Key: metadata key name.
/// Value: u64 value (used for counters like audit_sequence).
pub const METADATA: TableDefinition<&str, u64> = TableDefinition::new("metadata");

/// Note commitment tree: position (u64) -> 32-byte commitment hash.
///
/// Key: position in the append-only tree (0-based, monotonically increasing).
/// Value: 32-byte note commitment.
pub const NOTE_COMMITMENTS: TableDefinition<u64, &[u8; 32]> =
    TableDefinition::new("note_commitments");

/// Nullifier set: nullifier hash (32 bytes) -> unit (presence = spent).
///
/// Key: 32-byte nullifier hash.
/// Value: empty (presence in the table means the note is spent).
pub const NULLIFIERS: TableDefinition<&[u8; 32], ()> = TableDefinition::new("nullifiers");

/// Checkpoints: height (u64) -> serialized Checkpoint.
///
/// Key: checkpoint height (always a multiple of the checkpoint interval).
/// Value: postcard-serialized `dregg_federation::Checkpoint` struct.
pub const CHECKPOINTS: TableDefinition<u64, &[u8]> = TableDefinition::new("checkpoints");

/// Byte-blob metadata table for values that don't fit in a u64.
///
/// Key: metadata key name.
/// Value: arbitrary byte blob (e.g., cached Merkle roots).
pub const METADATA_BYTES: TableDefinition<&str, &[u8]> = TableDefinition::new("metadata_bytes");

// Metadata key constants.

/// Key for the latest attested root height.
pub const META_LATEST_ROOT_HEIGHT: &str = "latest_root_height";

/// Key for the note tree size (number of commitments).
pub const META_NOTE_TREE_SIZE: &str = "note_tree_size";

/// Key for the cached note tree root (stored in METADATA_BYTES).
pub const META_NOTE_TREE_ROOT_CACHE: &str = "note_tree_root_cache";

/// Key for the cached Poseidon2 note tree root (stored in METADATA_BYTES).
///
/// Stored as 4 bytes (little-endian u32) representing the BabyBear field element.
/// Updated on every `store_note_commitment` / `spend_note_atomic` call.
pub const META_POSEIDON2_NOTE_TREE_ROOT_CACHE: &str = "poseidon2_note_tree_root_cache";

/// Key for the latest checkpoint height.
pub const META_LATEST_CHECKPOINT_HEIGHT: &str = "latest_checkpoint_height";

/// Ledger checkpoints: height (u64) -> serialized LedgerCheckpoint.
///
/// Key: block height at which the checkpoint was taken.
/// Value: postcard-serialized `LedgerCheckpoint` struct (full ledger state snapshot).
pub const LEDGER_CHECKPOINTS: TableDefinition<u64, &[u8]> =
    TableDefinition::new("ledger_checkpoints");

/// Key for the latest ledger checkpoint height.
pub const META_LATEST_LEDGER_CHECKPOINT_HEIGHT: &str = "latest_ledger_checkpoint_height";

// ─── Blocklace Tables ──────────────────────────────────────────────────────

/// Blocklace blocks: block_id (32 bytes) -> serialized Block.
///
/// Key: 32-byte block ID (blake3 hash of signed content + signature).
/// Value: postcard-serialized `Block` struct.
pub const BLOCKLACE_BLOCKS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("blocklace_blocks");

/// Blocklace metadata: key (string) -> arbitrary bytes.
///
/// Stores tips, equivocators, ordering state, and other blocklace metadata.
/// Key: metadata key name (e.g., "meta").
/// Value: postcard-serialized `BlocklaceMeta` struct.
pub const BLOCKLACE_META: TableDefinition<&str, &[u8]> = TableDefinition::new("blocklace_meta");

/// Key for the blocklace metadata blob in the BLOCKLACE_META table.
pub const BLOCKLACE_META_KEY: &str = "meta";

/// Key for the executed_up_to index in the BLOCKLACE_META table.
///
/// LEGACY/diagnostic: a bare COUNT of executed blocks. It is no longer a resume
/// point — an index into the tau order is unsound as a cursor because the order
/// can shift under honest catch-up growth (the machine-checked counterexample in
/// `metatheory/Dregg2/Consensus/TauPrefixMonotone.lean`). Recovery resumes from
/// the identity set (`BLOCKLACE_EXECUTED_IDS_KEY` ∪ the commit log's block ids).
pub const BLOCKLACE_EXECUTED_UP_TO_KEY: &str = "executed_up_to";

/// Key for the executed finalized-block IDENTITY set in the BLOCKLACE_META
/// table (postcard-serialized `Vec<BlockId>`, first-served order). Together
/// with the commit log's per-turn `block_id`s, this is the crash-consistent
/// resume state for the node's identity execution cursor (the TauPrefixMonotone
/// closure: execution tracked by block id, never by position).
pub const BLOCKLACE_EXECUTED_IDS_KEY: &str = "executed_block_ids";

/// Node-local witnessed receipt artifacts.
///
/// Key: receipt hash.
/// Value: caller-owned serialized witness vector. The persist crate keeps this
/// table byte-oriented so it does not depend on `dregg-turn`.
pub const WITNESSED_RECEIPTS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("witnessed_receipts");

// ─── Durable Commit Log + Index (crash-consistency) ─────────────────────────
//
// The commit log is the authoritative, append-only record of finalized turns
// that THIS node has applied to its ledger. It is the recovery anchor: each
// record is written in the SAME redb transaction that advances the commit
// cursor (`META_COMMIT_CURSOR`), so the cursor and the per-turn record can
// never be torn against each other. The index tables below are secondary
// views derived from this log; every index write happens in that same
// transaction, so the "index entry exists iff the log has it" invariant holds
// by construction across crashes.

/// Commit log: commit ordinal (u64, 0-based, == position in the tau-finalized
/// order this node has applied) -> postcard-serialized `CommitRecord`.
///
/// Key: the commit ordinal (a dense, gap-free counter advanced by exactly one
/// per applied turn; equals the prior `executed_up_to` semantics but is now the
/// crash-consistent anchor written atomically with the record itself).
/// Value: postcard-serialized `commit_log::CommitRecord`.
pub const COMMIT_LOG: TableDefinition<u64, &[u8]> = TableDefinition::new("commit_log");

/// Index — receipt by hash: receipt_hash (32 bytes) -> commit ordinal (u64).
///
/// Lets a verifier/explorer resolve a receipt hash to its commit position in
/// O(1) without scanning. The pointed-to `CommitRecord` carries the full
/// coordinates (height, creator, turn hash, ledger root).
pub const IDX_RECEIPT_BY_HASH: TableDefinition<&[u8; 32], u64> =
    TableDefinition::new("idx_receipt_by_hash");

/// Index — turn by hash: turn_hash (32 bytes) -> commit ordinal (u64).
pub const IDX_TURN_BY_HASH: TableDefinition<&[u8; 32], u64> =
    TableDefinition::new("idx_turn_by_hash");

/// Index — turns by (height, creator): composite key -> commit ordinal (u64).
///
/// Key layout: 8-byte big-endian height ++ 32-byte creator ++ 8-byte
/// big-endian ordinal. Big-endian height makes redb's lexicographic range
/// scan equal a height-ordered scan, so "all turns at height H" and "all
/// turns by creator C in height order" are efficient range queries. The
/// trailing ordinal keeps keys unique when several turns commit at the same
/// `(height, creator)` — the normal case for ROUTE-level turns (the
/// trustline/court/channels services), several of which can commit between
/// two attested-height advances. Stores written with the older 40-byte key
/// are migrated by `migrate_height_creator_index` at open.
pub const IDX_TURN_BY_HEIGHT_CREATOR: TableDefinition<&[u8], u64> =
    TableDefinition::new("idx_turn_by_height_creator");

/// Index — cell by id (durable per-turn snapshot): cell_id (32 bytes) ->
/// postcard-serialized `dregg_cell::Cell`.
///
/// Updated atomically per applied turn from the executor's post-state so a
/// node can look up the current contents of ANY cell touched since the last
/// full ledger checkpoint, without replaying. Cells not touched since the last
/// checkpoint are served from the checkpoint; this table holds the deltas on
/// top of it. Rebuilt deterministically from the commit log on demand.
pub const IDX_CELL_BY_ID: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("idx_cell_by_id");

/// Key (in METADATA) for the durable commit cursor: the number of turns this
/// node has committed and indexed = the next free commit ordinal. This is the
/// crash-consistent replacement for the separately-written
/// `BLOCKLACE_EXECUTED_UP_TO_KEY`; recovery reads THIS value (advanced inside
/// the per-turn commit transaction) as the authoritative high-water mark.
pub const META_COMMIT_CURSOR: &str = "commit_cursor";

/// Key (in METADATA) for the durable commit-log COMPACTION FLOOR: the number of
/// commit records that have been compacted away (`compact_below`) because a
/// finalized ledger checkpoint at/above their height subsumes them. Equals the
/// lowest commit ordinal still physically present in [`COMMIT_LOG`]: every
/// ordinal in `[compacted_floor, commit_cursor)` resolves to a record; ordinals
/// in `[0, compacted_floor)` were compacted (their finalized state lives in the
/// checkpoint). 0 on a node that has never compacted. NEVER advances the cursor.
///
/// The post-compaction index-audit density invariant is
/// `commit_cursor() == commit_log.len() + compacted_floor` (the pre-compaction
/// `cursor == len` is the `compacted_floor == 0` special case).
pub const META_COMMIT_COMPACTED: &str = "commit_compacted_floor";

/// Compacted turn block-ids: the blocklace `block_id` of every turn whose commit
/// record was compacted away (presence = a turn this node DURABLY APPLIED whose
/// record is no longer in [`COMMIT_LOG`] because a checkpoint subsumes it).
///
/// This is load-bearing for **no-double-apply**: the node's identity execution
/// cursor (`node/src/execution_cursor.rs`) re-executes a turn block on recovery
/// iff its id is NOT among the durable applied-turn ids, and the persist-side
/// source of those ids is [`PersistentStore::commit_log_block_ids`]. Compacting
/// a record removes its id from the live commit log, so this set carries it
/// forward: `commit_log_block_ids` returns the SURVIVORS' ids ∪ this set, i.e.
/// the full set of applied-turn ids, unchanged by compaction. Without it, a
/// compacted (already-applied) turn would look un-executed and be re-applied on
/// top of the checkpoint that already includes it (a double-apply).
///
/// Key: 32-byte turn block id. Value: unit (presence = compacted-but-applied).
pub const COMMIT_COMPACTED_BLOCK_IDS: TableDefinition<&[u8; 32], ()> =
    TableDefinition::new("commit_compacted_block_ids");

// ─── Forever-Digest Sets (restart-durable anti-replay carriers) ──────────────
//
// Several node registries carry "burned forever" digest sets whose refusal
// semantics must survive a process restart: the trustline draw / rebuild /
// settle-unapplied digests (Lean `no_double_draw_forever`,
// `draw_replay_refused_across_epochs` — the slice's own debit list resets at
// every rebalance epoch, so the FOREVER property needs a carrier that does
// not) and the equivocation court's resolved-evidence digests (no-double-
// resolve / no-double-slash). These are NOT derivable from the cells: the
// cell holds only the LAST digest (`TL_DIGEST_SLOT`) and the court's verdicts
// move value without leaving the full digest set on any cell. See
// `docs/PERSISTENCE.md`.

/// Forever-burned digest sets, namespaced per registry and scoped per cell.
///
/// Key layout: 1-byte namespace ++ 32-byte scope ++ 32-byte digest = 65 bytes.
/// Value: unit (presence = burned).
///
/// The scope is the cell the digest was burned against (the trustline cell id
/// for `NS_TRUSTLINE_DIGEST`); namespaces whose digests are global use the
/// all-zero scope.
pub const FOREVER_DIGESTS: TableDefinition<&[u8; 65], ()> = TableDefinition::new("forever_digests");

/// Namespace byte: the node's trustline digest registry (committed draws,
/// shadow-rebuild digests, settle-unapplied compensation digests — everything
/// `TrustlineRegistry::record_digest` burns).
pub const NS_TRUSTLINE_DIGEST: u8 = 1;

/// Namespace byte: the equivocation court's resolved-evidence digests
/// (scope = all-zero; evidence digests are global, not per-cell).
pub const NS_COURT_RESOLVED: u8 = 2;

// ─── Durable Channel Rosters (docs/PERSISTENCE.md §3, the roster caveat) ─────
//
// The channel-group cell holds only the roster's COMMITMENT
// (`CH_MEMBER_ROOT_SLOT`); the member→seal-pk CONTENT is node-held and
// verifiable-but-not-derivable from the cell. This table is the durable
// carrier: written after every committed epoch step, re-committed against the
// on-cell root at load (a stale durable roster is DISCARDED, fail-closed —
// `RosterStale` then means genuine divergence, not a mere restart).

/// Channel rosters: channel cell id (32 bytes) -> postcard-serialized roster
/// (`BTreeMap<CellId, [u8; 32]>` — member cell → X25519 seal pk).
pub const CHANNEL_ROSTERS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("channel_rosters");
