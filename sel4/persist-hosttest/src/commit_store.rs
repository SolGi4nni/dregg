//! `commit_store` — the persist-PD's durable verified commit-log + the Tier-C
//! chain gate, `no_std` + `alloc`, ready to ride INSIDE the seL4 persist PD.
//!
//! This is the persist-PD's *missing organ*. The seat in `sel4/dregg.system`
//! (`sel4/dregg-pd/persist-stub/`) maps `commit_out` (R) and reads one sentinel
//! byte — it holds the durable-store SEAT but stores NOTHING. The real persist-PD
//! is "the durable store: commit log, checkpoints, snapshot⊕overlay + root tooth"
//! (FIRMAMENT §2 line 81) and writes the commit record in ONE redb transaction
//! *before the turn returns* — the `n = 1` **synchronous commit** property
//! (FIRMAMENT §3 line 135). This module is that store's logic, transport-free, so
//! the same code runs in the host witness here AND (via `#[path]` include) inside
//! the persist PD once the redb-over-block-cap backend (`docs/SEL4-EMBEDDING.md`
//! §3) lands under it.
//!
//! THE DISCIPLINE IS REUSED, NOT REINVENTED. Every gate below is the EXACT
//! discipline the live pg-dregg + persist stack already enforces:
//!
//!  - the chain gate is `pg-dregg/src/mirror.rs`'s `RootChain::extend` /
//!    `verify_chain_step` (the anti-substitution tooth: `prev_root == head` AND
//!    `ordinal == next_ordinal`, fail-closed `ChainRefusal`);
//!  - the commit record is `persist/src/commit_log.rs`'s `CommitRecord` (ordinal ·
//!    height · block_id · turn_hash · creator · receipt_hash · ledger_root, here
//!    plus the explicit `prev_root` that `pg-dregg`'s `TurnRow` carries so the
//!    chain is checkable on the rows alone);
//!  - the append is `commit_finalized_turn_with_burns`'s ONE-TRANSACTION
//!    discipline: the `expected_ordinal == cursor` torn-state guard, the
//!    idempotent-replay branch (same `turn_hash` ⇒ no-op success; different ⇒
//!    Integrity error), the append-then-index-then-advance-cursor-LAST ordering.
//!
//! The `BTreeMap`-backed store here stands in for the redb tables; on-device the
//! persist PD swaps the map for `redb` over the block cap it solely holds, and the
//! `commit()` fsync boundary becomes the durable one. The GATE LOGIC — what makes
//! a turn admissible at all — is byte-identical, which is the whole point: the
//! persist PD enforces the SAME spine the pg verified store does.

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

/// The genesis pre-state root — turn 0 chains onto "nothing".
/// (`pg-dregg/src/workflow.rs`: `pub const GENESIS_ROOT: [u8; 32] = [0u8; 32];`.)
pub const GENESIS_ROOT: [u8; 32] = [0u8; 32];

/// The durable per-turn record — the seL4 analogue of `dregg.turns` / the node's
/// `CommitRecord` (`persist/src/commit_log.rs`). One row per `ordinal`.
///
/// `ledger_root` is the POST-state root; it becomes the next turn's `prev_root`
/// (FIRMAMENT §3 line 240: `CommitRecord::ledger_root` is the post-state binding).
/// Carrying `prev_root` explicitly — as `pg-dregg`'s `TurnRow` does — makes the
/// chain checkable from the rows alone (a light client walking the log), which is
/// the §10 "self-checking projection" property.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitRecord {
    /// Dense, gap-free position in applied order (the key into the log).
    pub ordinal: u64,
    /// Attested-root height (the `(height, creator)` index axis).
    pub height: u64,
    /// Consensus anchor (the blocklace block id).
    pub block_id: [u8; 32],
    /// Turn identity (the by-hash index key + the idempotent-replay discriminator).
    pub turn_hash: [u8; 32],
    /// Acting agent / creator cell id (provenance).
    pub creator: [u8; 32],
    /// Receipt identity (the receipt-by-hash index key).
    pub receipt_hash: [u8; 32],
    /// PRE-state root: MUST equal the prior turn's `ledger_root` (the chain tooth).
    pub prev_root: [u8; 32],
    /// POST-state root: becomes the next turn's `prev_root`.
    pub ledger_root: [u8; 32],
    /// Post-state snapshots of the mutated cells, opaque bytes here (the persist
    /// PD stores `touched_cells: Vec<Cell>`; the store does not interpret them).
    pub touched_cells: Vec<u8>,
}

/// Why a turn was refused at the chain gate — the EXACT shape of
/// `pg-dregg/src/mirror.rs`'s `ChainRefusal`. Fail-closed: the head never moves
/// on a refusal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChainRefusal {
    /// `ordinal != next_ordinal` — the log is dense and gap-free; no holes.
    OrdinalGap { expected: u64, got: u64 },
    /// `prev_root != head` — the post-state of turn N is the pre-state of N+1.
    /// This is the anti-substitution tooth: a turn that does not chain is forged
    /// relative to the committed head, and is refused.
    RootMismatch { head: [u8; 32], prev: [u8; 32] },
    /// A torn-state / double-apply violation at the durable cursor (the
    /// `commit_finalized_turn_with_burns` Integrity errors).
    Integrity(String),
}

impl ChainRefusal {
    pub fn reason(&self) -> String {
        match self {
            ChainRefusal::OrdinalGap { expected, got } => {
                format!("ordinal gap: expected {expected}, got {got}")
            }
            ChainRefusal::RootMismatch { head, prev } => format!(
                "root mismatch: head {} != turn.prev_root {}",
                hex8(head),
                hex8(prev)
            ),
            ChainRefusal::Integrity(m) => format!("integrity: {m}"),
        }
    }
}

/// The pure chain-step gate — VERBATIM the logic of
/// `pg-dregg/src/mirror.rs::verify_chain_step` (the gate lifted into the pg
/// `dregg_verify_turn` SQL function). `head == None` is genesis (pass-through on
/// the root, the ordinal still checked); non-genesis requires exact `prev_root ==
/// head`. Fail-closed: any deviation is a refusal.
pub fn verify_chain_step(
    head: Option<[u8; 32]>,
    next_ordinal: u64,
    prev_root: [u8; 32],
    ordinal: u64,
) -> Result<(), ChainRefusal> {
    if ordinal != next_ordinal {
        return Err(ChainRefusal::OrdinalGap {
            expected: next_ordinal,
            got: ordinal,
        });
    }
    if let Some(head) = head {
        if prev_root != head {
            return Err(ChainRefusal::RootMismatch {
                head,
                prev: prev_root,
            });
        }
    }
    Ok(())
}

/// The durable verified commit-log store the persist PD owns.
///
/// `BTreeMap` stands in for the redb tables (the persist PD swaps it for `redb`
/// over the block cap). The three secondary indices mirror
/// `persist/src/commit_log.rs` (receipt-by-hash, turn-by-hash, and — surfaced as
/// `head`/`cursor` here — the metadata cursor). Reads are free; writes pass the
/// chain gate.
pub struct CommitStore {
    /// The commit log: ordinal -> record (the redb `COMMIT_LOG` table).
    log: BTreeMap<u64, CommitRecord>,
    /// turn_hash -> ordinal (the redb `IDX_TURN_BY_HASH` table).
    by_turn_hash: BTreeMap<[u8; 32], u64>,
    /// receipt_hash -> ordinal (the redb `IDX_RECEIPT_BY_HASH` table).
    by_receipt_hash: BTreeMap<[u8; 32], u64>,
    /// The durable cursor = next free ordinal = number of committed turns
    /// (`persist`'s `META_COMMIT_CURSOR`; `commit_cursor()`).
    cursor: u64,
    /// The current chain head = the last committed turn's `ledger_root`
    /// (None = genesis). The `RootChain::head` the chain gate checks against.
    head: Option<[u8; 32]>,
}

impl Default for CommitStore {
    fn default() -> Self {
        Self::new()
    }
}

impl CommitStore {
    pub fn new() -> Self {
        CommitStore {
            log: BTreeMap::new(),
            by_turn_hash: BTreeMap::new(),
            by_receipt_hash: BTreeMap::new(),
            cursor: 0,
            head: None,
        }
    }

    /// Resume from a durable head + cursor (a persist PD restart reads the
    /// max-ordinal record and resumes — `pg-dregg`'s `Drainer::resume_chain` /
    /// `RootChain::resume`; `persist`'s `commit_cursor()` recovery).
    pub fn resume(head: Option<[u8; 32]>, next_ordinal: u64) -> Self {
        CommitStore {
            log: BTreeMap::new(),
            by_turn_hash: BTreeMap::new(),
            by_receipt_hash: BTreeMap::new(),
            cursor: next_ordinal,
            head,
        }
    }

    // ---- reads are FREE (the spine: `SELECT` cannot break a transition-fn
    //      invariant; it only observes the materialized state) ------------------

    /// The next free ordinal = number of durably committed turns.
    pub fn commit_cursor(&self) -> u64 {
        self.cursor
    }

    /// The current chain head (the last committed `ledger_root`), or None at
    /// genesis.
    pub fn head_root(&self) -> Option<[u8; 32]> {
        self.head
    }

    /// Read a committed turn by its position (the `dregg.turns` row read).
    pub fn lookup_by_ordinal(&self, ordinal: u64) -> Option<&CommitRecord> {
        self.log.get(&ordinal)
    }

    /// Read a committed turn by its identity (the `IDX_TURN_BY_HASH` lookup).
    pub fn lookup_by_turn_hash(&self, turn_hash: &[u8; 32]) -> Option<&CommitRecord> {
        let ord = self.by_turn_hash.get(turn_hash)?;
        self.log.get(ord)
    }

    /// Read a committed turn by its receipt (the `IDX_RECEIPT_BY_HASH` lookup).
    pub fn lookup_by_receipt_hash(&self, receipt_hash: &[u8; 32]) -> Option<&CommitRecord> {
        let ord = self.by_receipt_hash.get(receipt_hash)?;
        self.log.get(ord)
    }

    /// The whole log in applied order — a light client walks this and re-checks
    /// the root chain (`prev_root[N+1] == ledger_root[N]`) to detect a tampered
    /// store. The "self-checking projection" property (§10).
    pub fn iter_ordered(&self) -> impl Iterator<Item = (&u64, &CommitRecord)> {
        self.log.iter()
    }

    // ---- writes pass the CHAIN GATE then commit ATOMICALLY -------------------

    /// Commit a verified turn — the persist PD's `n = 1` synchronous commit. This
    /// is the ONLY door state enters the durable store, and it runs the SAME gate
    /// the pg verified store's `dregg.commit_log` trigger runs:
    ///
    /// 1. **the chain gate** (`verify_chain_step`) — `ordinal == cursor` AND
    ///    `prev_root == head`; a non-chaining / out-of-order turn is REFUSED, the
    ///    head does not move (`RootChain::extend`);
    /// 2. **the torn-state / idempotent-replay guard** (the
    ///    `commit_finalized_turn_with_burns` discipline) — `expected_ordinal`
    ///    (carried as `record.ordinal`) must equal the durable `cursor`; a replay
    ///    of an already-committed ordinal with the SAME `turn_hash` is a no-op
    ///    success, a DIFFERENT `turn_hash` at a taken ordinal is an Integrity
    ///    refusal;
    /// 3. **the append** — record + the two by-hash indices land together, then
    ///    the cursor advances LAST and the head moves to the new `ledger_root`
    ///    (the one-transaction ordering; on-device this is one redb `commit()`).
    ///
    /// Returns the assigned ordinal on success.
    pub fn commit_verified_turn(&mut self, record: &CommitRecord) -> Result<u64, ChainRefusal> {
        // (2a) torn-state / idempotent-replay guard, BEFORE the chain gate, so a
        //      replay of an already-durable turn short-circuits to success rather
        //      than tripping a RootMismatch against the advanced head.
        if record.ordinal != self.cursor {
            if record.ordinal < self.cursor {
                // An ordinal already holds a record. Idempotent iff same turn.
                match self.log.get(&record.ordinal) {
                    Some(existing) if existing.turn_hash == record.turn_hash => {
                        return Ok(record.ordinal); // already committed; no-op success
                    }
                    Some(_) => {
                        return Err(ChainRefusal::Integrity(format!(
                            "ordinal {} already holds a different turn",
                            record.ordinal
                        )));
                    }
                    None => {
                        return Err(ChainRefusal::Integrity(format!(
                            "cursor {} > ordinal {} but no record there (corrupt log)",
                            self.cursor, record.ordinal
                        )));
                    }
                }
            }
            // ordinal > cursor: refusing to write a gap (no holes in the log).
            return Err(ChainRefusal::Integrity(format!(
                "expected ordinal {} != durable cursor {}; refusing to write a gap",
                record.ordinal, self.cursor
            )));
        }

        // (1) THE CHAIN GATE — the anti-substitution tooth.
        verify_chain_step(self.head, self.cursor, record.prev_root, record.ordinal)?;

        // (3) THE ATOMIC APPEND — log + indices together, cursor + head LAST.
        // (On-device: ONE redb write transaction; here: one synchronous block.)
        let assigned = self.cursor;
        let stored = CommitRecord {
            ordinal: assigned,
            ..record.clone()
        };
        self.by_turn_hash.insert(stored.turn_hash, assigned);
        self.by_receipt_hash.insert(stored.receipt_hash, assigned);
        self.log.insert(assigned, stored.clone());
        self.cursor = assigned + 1; // advance the durable cursor LAST
        self.head = Some(stored.ledger_root); // the head moves only on success
        Ok(assigned)
    }
}

/// First-8-hex helper for refusal messages (alloc-only, no_std-safe).
fn hex8(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(8);
    for byte in b.iter().take(4) {
        s.push(nib(byte >> 4));
        s.push(nib(byte & 0xf));
    }
    s
}

fn nib(n: u8) -> char {
    match n {
        0..=9 => (b'0' + n) as char,
        _ => (b'a' + (n - 10)) as char,
    }
}
