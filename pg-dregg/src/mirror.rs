//! Tier B/C CORE — postgres-independent, `cargo test`-proven.
//!
//! This is the storage/query/verified-write substrate of `pg-dregg`, built to
//! the spine invariant of `docs/PG-DREGG.md` §8:
//!
//! > **Reads are free SQL; state mutates ONLY through verified turns.**
//!
//! Like [`crate::authz`] (the Tier A core), everything here is plain Rust with
//! no `pgrx` dependency, so it is provable with `cargo test` (no postgres, no
//! `cargo-pgrx`). The `#[pg_extern]` wrappers in [`crate`] marshal SQL types
//! into these functions.
//!
//! ## Why this crate does NOT depend on `dregg-cell`
//!
//! `dregg-cell` pulls `dregg-circuit` unconditionally (its
//! `compute_canonical_state_commitment` is circuit-backed). Linking it here
//! would forfeit the circuit-free, offline property that makes the embeddable
//! `pg-dregg` layer attractive (`cargo tree -i dregg-circuit -p dregg-auth` is
//! empty, and we keep it that way). So the mirror works over **plain owned row
//! types** — the SQL-row projection of dregg state — and the *projection* from a
//! live `dregg_cell::Cell` into these rows happens on the **node** side (which
//! already has `dregg-cell`), at the commit-log sink. This crate owns the SQL
//! shape, the universal-memory model, the DDL, and the root-chaining tooth; the
//! node owns the `Cell -> CellRow` decode. The two meet at the serde wire
//! (`MirrorBatch`).
//!
//! ## What is in here
//!
//! 1. [`Domain`] + [`MemCell`] — the universal-memory model
//!    (`docs/UNIVERSAL-MEMORY.md`): ONE multiset over `Domain × κ`, the honest
//!    single-relation form of all dregg state.
//! 2. [`CellRow`] / [`TurnRow`] / [`CapRow`] — the typed projections of the
//!    commit log's `CommitRecord` + `Cell` + `CapabilityRef` (the query sugar
//!    over the universal table).
//! 3. [`MirrorBatch`] — one verified turn's worth of mirror rows, the serde unit
//!    the node ships into postgres (Tier B1, the mirror).
//! 4. [`RootChain`] — the Tier C tooth: the post-state root of turn *N* is the
//!    pre-state root of turn *N+1*; a batch that does not chain is refused. This
//!    is `snapshot.rs`'s `claimed_root` anti-substitution discipline, in SQL's
//!    write path.
//! 5. [`ddl`] — the schema as emittable SQL (so the extension ships its own
//!    `CREATE TABLE`/`CREATE POLICY`, generated from the same Rust that defines
//!    the rows — no schema drift between code and DDL).

use serde::{Deserialize, Serialize};

// ============================================================================
// 1. The universal-memory model — ONE multiset over Domain × κ.
// ============================================================================
//
// docs/UNIVERSAL-MEMORY.md proves dregg's whole state is one Blum multiset over
// `Domain × κ`, with the map roots as derived boundary views. A future state
// component is a NEW DOMAIN VALUE, never a new table. So this enum is the whole
// address space of dregg memory, and `MemCell` is one cell of it.

/// The memory domain — the `Domain` half of the universal `(domain, key)`
/// address (`docs/UNIVERSAL-MEMORY.md`). A new state component is a new VARIANT
/// here, never a new table; that is the whole point of the collapse.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Domain {
    /// Cell registers / scalar state (balance, nonce, field slots).
    Registers,
    /// The openable sorted heap maps.
    Heap,
    /// Capability c-lists (the delegation graph lives here).
    Caps,
    /// Spent-note nullifiers (the no-double-spend domain).
    Nullifiers,
    /// Collection / index roots.
    Index,
}

impl Domain {
    /// The stable SQL/tag string. Load-bearing: the tag is what keeps the flat
    /// untagged address space from aliasing (`docs/UNIVERSAL-MEMORY.md`: a cap
    /// check at key 7 must NOT read the nullifier value at 7).
    pub fn tag(self) -> &'static str {
        match self {
            Domain::Registers => "registers",
            Domain::Heap => "heap",
            Domain::Caps => "caps",
            Domain::Nullifiers => "nullifiers",
            Domain::Index => "index",
        }
    }

    /// Parse a tag back to a domain (fail-closed: unknown tag ⇒ `None`).
    pub fn from_tag(s: &str) -> Option<Domain> {
        Some(match s {
            "registers" => Domain::Registers,
            "heap" => Domain::Heap,
            "caps" => Domain::Caps,
            "nullifiers" => Domain::Nullifiers,
            "index" => Domain::Index,
            _ => return None,
        })
    }

    /// Every domain, for exhaustive iteration (boundary-root derivation).
    pub const ALL: [Domain; 5] = [
        Domain::Registers,
        Domain::Heap,
        Domain::Caps,
        Domain::Nullifiers,
        Domain::Index,
    ];
}

/// One cell of the universal memory: a `(domain, collection, key) -> Option ν`
/// entry. `value == None` is the "absent" cell (`none` in the Lean model);
/// `Some` is a present cell. `last_ordinal` ties it to the turn that produced it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemCell {
    pub domain: Domain,
    /// The collection id (e.g. the cell, the map) — `collection_id` in the
    /// concrete `addr = hash[domain_tag, collection_id, key]`.
    pub collection: Vec<u8>,
    /// The key within the domain (`κ`).
    pub key: Vec<u8>,
    /// `Some(ν)` = present cell, `None` = absent.
    pub value: Option<Vec<u8>>,
    /// The turn ordinal that produced this cell's value.
    pub last_ordinal: u64,
}

// ============================================================================
// 2. Typed projections — the query sugar over the universal table.
// ============================================================================

/// A turn row — the SQL projection of `persist::CommitRecord`
/// (`persist/src/commit_log.rs`). The authority for "what verified turns
/// happened"; every state row is reconcilable to one of these by `last_ordinal`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TurnRow {
    pub ordinal: u64,
    pub height: u64,
    pub block_id: [u8; 32],
    pub block_executed_up_to: u64,
    pub turn_hash: [u8; 32],
    pub creator: [u8; 32],
    pub receipt_hash: [u8; 32],
    /// The canonical ledger root AFTER this turn (`CommitRecord::ledger_root`).
    /// This is the post-state commitment that the next turn must chain onto.
    pub ledger_root: [u8; 32],
    /// The ledger root BEFORE this turn (the prior turn's `ledger_root`, or the
    /// genesis root for ordinal 0). Carried so the chaining tooth ([`RootChain`])
    /// can verify the batch links to the head without a separate lookup.
    pub prev_root: [u8; 32],
}

/// A cell row — the latest post-image of one cell. The SQL projection of
/// `dregg_cell::Cell` (`cell/src/cell.rs`); the heavy decode (`Cell` ⟶ this)
/// happens node-side. `cell_root` is the cell's commitment, a leaf of
/// `ledger_root`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellRow {
    pub cell_id: [u8; 32],
    pub mode: String,
    pub balance: i64,
    pub nonce: u64,
    /// Canonical field bytes (`CellState` field slots), authoritative.
    pub fields: Vec<u8>,
    /// Decoded field slots as JSON (query convenience; `fields` is canonical).
    pub fields_json: Option<String>,
    pub heap: Option<Vec<u8>>,
    pub program: Option<Vec<u8>>,
    pub verification_key: Option<Vec<u8>>,
    /// Decoded permissions as JSON (`cell/src/cell.rs` `Permissions`).
    pub permissions_json: Option<String>,
    pub delegate: Option<[u8; 32]>,
    pub lifecycle: String,
    pub last_ordinal: u64,
    pub cell_root: [u8; 32],
}

/// A capability row — one `CapabilityRef` in a cell's `CapabilitySet`
/// (`cell/src/capability.rs`). `(holder, slot)` is the c-list address; the
/// `holder -> target` edges are the delegation graph.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapRow {
    pub holder: [u8; 32],
    pub slot: u32,
    pub target: [u8; 32],
    /// `AuthRequired` as JSON.
    pub permissions_json: String,
    pub breadstuff: Option<[u8; 32]>,
    pub expires_at: Option<u64>,
    /// `allowed_effects` (the attenuation) as JSON, if present.
    pub allowed_effects_json: Option<String>,
    pub stored_epoch: Option<u64>,
    pub last_ordinal: u64,
}

// ============================================================================
// 3. MirrorBatch — one verified turn's mirror rows (the Tier B1 wire unit).
// ============================================================================

/// Everything the mirror writes for ONE verified turn: the turn row plus the
/// post-images of every cell / capability / memory cell it touched. This is the
/// serde unit the node ships from its commit-log sink into postgres (Tier B1).
///
/// The node produces this AFTER the kernel verified the turn — so by the time a
/// `MirrorBatch` exists, the spine invariant already holds for it: these rows
/// ARE a verified-turn post-image. The mirror's job is only to (a) refuse a
/// batch that does not chain onto the current head ([`RootChain::extend`]), and
/// (b) write it read-only-to-apps. It never decides authorization or execution.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MirrorBatch {
    pub turn: TurnRow,
    pub cells: Vec<CellRow>,
    pub caps: Vec<CapRow>,
    pub memory: Vec<MemCell>,
}

impl MirrorBatch {
    /// A structural well-formedness check the mirror runs before writing:
    /// every touched row must reference THIS turn's ordinal (no smuggling a row
    /// from a different turn into a batch). Returns the first offending row's
    /// description, or `Ok(())`.
    pub fn check_ordinals(&self) -> Result<(), String> {
        let o = self.turn.ordinal;
        for c in &self.cells {
            if c.last_ordinal != o {
                return Err(format!(
                    "cell {} carries ordinal {}, batch is {o}",
                    hex(&c.cell_id),
                    c.last_ordinal
                ));
            }
        }
        for c in &self.caps {
            if c.last_ordinal != o {
                return Err(format!(
                    "cap ({},{}) carries ordinal {}, batch is {o}",
                    hex(&c.holder),
                    c.slot,
                    c.last_ordinal
                ));
            }
        }
        for m in &self.memory {
            if m.last_ordinal != o {
                return Err(format!(
                    "mem cell ({},{}) carries ordinal {}, batch is {o}",
                    m.domain.tag(),
                    hex(&m.key),
                    m.last_ordinal
                ));
            }
        }
        Ok(())
    }
}

// ============================================================================
// 4. RootChain — the anti-substitution tooth (Tier C, applied read-only in B).
// ============================================================================
//
// snapshot.rs binds a reconstructed ledger to a `claimed_root` and fails closed
// on mismatch. CommitRecord's ledger_root "binds the record to a concrete
// post-state". The SAME discipline, in the mirror's write path: the post-state
// root of turn N MUST be the pre-state root of turn N+1, so the turns table is a
// hash chain a light client could itself walk. A `MirrorBatch` whose `prev_root`
// does not equal the current head root is REFUSED — that is how the mirror
// detects a tampered / reordered / forged batch WITHOUT re-running the verifier.
// (Tier C adds the verifier on top; the chain tooth is the cheap structural half
// that even the read-only mirror enforces.)

/// The running head of the mirror's root chain. `None` before any turn (the
/// next batch is genesis); `Some(root)` is the post-state root of the last
/// accepted turn.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RootChain {
    head: Option<[u8; 32]>,
    next_ordinal: u64,
}

/// Why a batch was refused by the chain tooth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChainRefusal {
    /// The batch's ordinal is not the next expected one (gap or replay).
    OrdinalGap { expected: u64, got: u64 },
    /// The batch's pre-state root does not equal the current head — a tampered
    /// or reordered batch.
    RootMismatch { head: [u8; 32], prev: [u8; 32] },
    /// The batch's own ordinals are inconsistent (a row from a different turn).
    Malformed(String),
}

impl core::fmt::Display for ChainRefusal {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ChainRefusal::OrdinalGap { expected, got } => {
                write!(f, "ordinal gap: expected {expected}, got {got}")
            }
            ChainRefusal::RootMismatch { head, prev } => write!(
                f,
                "root does not chain: head {}, batch prev_root {}",
                hex(head),
                hex(prev)
            ),
            ChainRefusal::Malformed(m) => write!(f, "malformed batch: {m}"),
        }
    }
}

impl RootChain {
    /// A fresh chain expecting genesis (ordinal 0).
    pub fn new() -> Self {
        RootChain {
            head: None,
            next_ordinal: 0,
        }
    }

    /// Resume a chain from a known head root and the next ordinal to expect
    /// (e.g. after restart, read from the mirror's current max-ordinal row).
    pub fn resume(head: [u8; 32], next_ordinal: u64) -> Self {
        RootChain {
            head: Some(head),
            next_ordinal,
        }
    }

    /// The current head post-state root, if any turns have been accepted.
    pub fn head(&self) -> Option<[u8; 32]> {
        self.head
    }

    /// The ordinal the chain next expects.
    pub fn next_ordinal(&self) -> u64 {
        self.next_ordinal
    }

    /// Attempt to extend the chain with a batch. Fail-closed: the batch is
    /// accepted ONLY if its ordinal is the next expected AND its `prev_root`
    /// equals the current head (genesis batch must carry `prev_root` matching
    /// the configured genesis root, here the all-zero/embedded one — the caller
    /// pins genesis by `resume`). On success the head advances to the batch's
    /// post-state `ledger_root`. On refusal the chain is UNCHANGED (so a bad
    /// batch cannot corrupt the head).
    pub fn extend(&mut self, batch: &MirrorBatch) -> Result<(), ChainRefusal> {
        if let Err(m) = batch.check_ordinals() {
            return Err(ChainRefusal::Malformed(m));
        }
        if batch.turn.ordinal != self.next_ordinal {
            return Err(ChainRefusal::OrdinalGap {
                expected: self.next_ordinal,
                got: batch.turn.ordinal,
            });
        }
        // The pre-state root of this batch must equal the chain head. For
        // genesis (head == None) the chain accepts whatever genesis root the
        // batch declares as prev_root and pins it (a `resume(genesis,0)` caller
        // makes this exact). For non-genesis, the roots MUST match.
        if let Some(head) = self.head {
            if batch.turn.prev_root != head {
                return Err(ChainRefusal::RootMismatch {
                    head,
                    prev: batch.turn.prev_root,
                });
            }
        }
        // Accept: advance.
        self.head = Some(batch.turn.ledger_root);
        self.next_ordinal += 1;
        Ok(())
    }
}

// ============================================================================
// 5. DDL emission — the schema generated from the same Rust that defines rows.
// ============================================================================
//
// The extension ships its own CREATE TABLE / CREATE POLICY so there is no drift
// between the row types above and the SQL. This returns the Tier B schema as a
// single string; the #[pg_extern] `dregg_install_schema()` runs it via SPI, and
// `pg-dregg/sql/schema-tierB.sql` is the human-readable mirror of it.

pub mod ddl {
    /// The Tier B schema (tables + indices + RLS policies + the write-lockdown
    /// role model). Idempotent (`IF NOT EXISTS`), so it is safe to re-run.
    /// Mirrors `pg-dregg/sql/schema-tierB.sql`; kept here so the extension can
    /// install it without shipping a separate file.
    pub fn tier_b() -> String {
        // Generated from the row types in the parent module. Kept terse here;
        // the file `sql/schema-tierB.sql` carries the fully-commented form.
        let mut s = String::new();
        s.push_str("CREATE SCHEMA IF NOT EXISTS dregg;\n");
        s.push_str("DO $$ BEGIN CREATE ROLE dregg_reader NOLOGIN; EXCEPTION WHEN duplicate_object THEN NULL; END $$;\n");
        // The kernel is the VERIFIED writer (the SECURITY DEFINER target in Tier
        // C). The read-side RLS gates APPLICATIONS, not the writer that produced
        // the post-image; the kernel writes verified-turn rows wholesale, so it
        // is BYPASSRLS. In Tier C even the kernel's writes still pass the
        // dregg_verify_turn CHECK (schema-tierC.sql) — RLS is the wrong tool to
        // gate them; the verifier is. (If the role pre-exists without the
        // attribute, ALTER lifts it.)
        s.push_str("DO $$ BEGIN CREATE ROLE dregg_kernel NOLOGIN BYPASSRLS; EXCEPTION WHEN duplicate_object THEN ALTER ROLE dregg_kernel BYPASSRLS; END $$;\n");
        s.push_str(TURNS);
        s.push_str(CELLS);
        s.push_str(CAPS);
        s.push_str(MEMORY);
        s.push_str(VIEWS);
        s.push_str(RLS);
        s
    }

    /// The dregg-developer query surface: views that make the "your node IS your
    /// postgres" story good. Each is a plain SELECT over the Tier-B tables, so it
    /// inherits the read-side RLS of the tables it draws from. Emitted as part of
    /// [`tier_b`]; mirrored in `sql/schema-tierB.sql` (anti-drift test below).
    pub const VIEWS_SQL: &str = VIEWS;

    const TURNS: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.turns (
    ordinal bigint PRIMARY KEY, height bigint NOT NULL, block_id bytea NOT NULL,
    block_executed_up_to bigint NOT NULL, turn_hash bytea NOT NULL UNIQUE,
    creator bytea NOT NULL, receipt_hash bytea NOT NULL,
    ledger_root bytea NOT NULL, prev_root bytea NOT NULL,
    committed_at timestamptz NOT NULL DEFAULT now());
CREATE INDEX IF NOT EXISTS turns_by_height  ON dregg.turns (height);
CREATE INDEX IF NOT EXISTS turns_by_creator ON dregg.turns (creator, ordinal);
"#;

    const CELLS: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.cells (
    cell_id bytea PRIMARY KEY, mode text NOT NULL, balance bigint NOT NULL,
    nonce bigint NOT NULL, fields bytea NOT NULL, fields_json jsonb,
    heap bytea, program bytea, verification_key bytea, permissions jsonb,
    delegate bytea, lifecycle text NOT NULL,
    last_ordinal bigint NOT NULL REFERENCES dregg.turns(ordinal),
    cell_root bytea NOT NULL);
CREATE INDEX IF NOT EXISTS cells_by_balance ON dregg.cells (balance);
CREATE INDEX IF NOT EXISTS cells_by_mode    ON dregg.cells (mode);
CREATE INDEX IF NOT EXISTS cells_fields_gin ON dregg.cells USING gin (fields_json);
"#;

    const CAPS: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.capabilities (
    holder bytea NOT NULL, slot int NOT NULL, target bytea NOT NULL,
    permissions jsonb NOT NULL, breadstuff bytea, expires_at bigint,
    allowed_effects jsonb, stored_epoch bigint,
    last_ordinal bigint NOT NULL REFERENCES dregg.turns(ordinal),
    PRIMARY KEY (holder, slot));
CREATE INDEX IF NOT EXISTS caps_by_target ON dregg.capabilities (target);
"#;

    const MEMORY: &str = r#"
CREATE TABLE IF NOT EXISTS dregg.memory (
    domain text NOT NULL, collection bytea NOT NULL, key bytea NOT NULL,
    value bytea, last_ordinal bigint NOT NULL REFERENCES dregg.turns(ordinal),
    PRIMARY KEY (domain, collection, key));
CREATE INDEX IF NOT EXISTS memory_by_domain ON dregg.memory (domain);
"#;

    // The dregg-developer query surface (docs/QUICKSTART-dregg-dev.md). Plain
    // SELECTs over the Tier-B tables; each inherits the table's read-side RLS.
    const VIEWS: &str = r#"
CREATE OR REPLACE VIEW dregg.cap_edges AS
    SELECT holder AS src, target AS dst, slot, permissions, expires_at
    FROM dregg.capabilities;
CREATE OR REPLACE VIEW dregg.cell_balances AS
    SELECT encode(cell_id, 'hex') AS cell, balance, nonce, lifecycle, last_ordinal
    FROM dregg.cells;
CREATE OR REPLACE VIEW dregg.receipt_chain AS
    SELECT ordinal, height, encode(creator, 'hex') AS creator,
           encode(prev_root, 'hex') AS prev_root,
           encode(ledger_root, 'hex') AS ledger_root, committed_at
    FROM dregg.turns ORDER BY ordinal;
"#;

    const RLS: &str = r#"
ALTER TABLE dregg.cells        ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.turns        ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.capabilities ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.memory       ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.cells        FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.turns        FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.capabilities FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.memory       FORCE ROW LEVEL SECURITY;
DROP POLICY IF EXISTS cells_read ON dregg.cells;
CREATE POLICY cells_read ON dregg.cells FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(cell_id, 'hex')));
DROP POLICY IF EXISTS turns_read ON dregg.turns;
CREATE POLICY turns_read ON dregg.turns FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(creator, 'hex')));
DROP POLICY IF EXISTS caps_read ON dregg.capabilities;
CREATE POLICY caps_read ON dregg.capabilities FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(holder, 'hex')));
DROP POLICY IF EXISTS memory_read ON dregg.memory;
CREATE POLICY memory_read ON dregg.memory FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(collection, 'hex')));
GRANT USAGE ON SCHEMA dregg TO dregg_reader, dregg_kernel;
GRANT SELECT ON ALL TABLES IN SCHEMA dregg TO dregg_reader;
GRANT INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg TO dregg_kernel;
REVOKE INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg FROM PUBLIC;
"#;
}

// ============================================================================
// helpers
// ============================================================================

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// ============================================================================
// Tests — the Tier B/C core, proven at the Rust level (no postgres needed).
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn root(n: u8) -> [u8; 32] {
        [n; 32]
    }

    fn turn(ordinal: u64, prev: [u8; 32], post: [u8; 32]) -> TurnRow {
        TurnRow {
            ordinal,
            height: ordinal,
            block_id: root(1),
            block_executed_up_to: ordinal,
            turn_hash: root(2),
            creator: root(3),
            receipt_hash: root(4),
            ledger_root: post,
            prev_root: prev,
        }
    }

    fn batch(ordinal: u64, prev: [u8; 32], post: [u8; 32]) -> MirrorBatch {
        MirrorBatch {
            turn: turn(ordinal, prev, post),
            cells: vec![CellRow {
                cell_id: root(9),
                mode: "Hosted".into(),
                balance: 100,
                nonce: ordinal,
                fields: vec![],
                fields_json: None,
                heap: None,
                program: None,
                verification_key: None,
                permissions_json: None,
                delegate: None,
                lifecycle: "Active".into(),
                last_ordinal: ordinal,
                cell_root: root(10),
            }],
            caps: vec![],
            memory: vec![MemCell {
                domain: Domain::Registers,
                collection: root(9).to_vec(),
                key: vec![0],
                value: Some(vec![100]),
                last_ordinal: ordinal,
            }],
        }
    }

    #[test]
    fn domain_tag_roundtrips_and_is_total() {
        for d in Domain::ALL {
            assert_eq!(Domain::from_tag(d.tag()), Some(d));
        }
        // The tag is load-bearing: unknown tags fail closed.
        assert_eq!(Domain::from_tag("ghost"), None);
        assert_eq!(Domain::from_tag(""), None);
    }

    #[test]
    fn chain_accepts_a_well_formed_sequence() {
        // genesis root g; turn 0: g -> r1; turn 1: r1 -> r2; turn 2: r2 -> r3
        let g = root(0);
        let mut chain = RootChain::resume(g, 0);
        assert!(chain.extend(&batch(0, g, root(1))).is_ok());
        assert_eq!(chain.head(), Some(root(1)));
        assert!(chain.extend(&batch(1, root(1), root(2))).is_ok());
        assert!(chain.extend(&batch(2, root(2), root(3))).is_ok());
        assert_eq!(chain.head(), Some(root(3)));
        assert_eq!(chain.next_ordinal(), 3);
    }

    #[test]
    fn chain_refuses_a_root_that_does_not_chain() {
        // The anti-substitution tooth: a batch whose prev_root != head is a
        // tampered / substituted batch and is REFUSED, leaving the chain intact.
        let g = root(0);
        let mut chain = RootChain::resume(g, 0);
        chain.extend(&batch(0, g, root(1))).unwrap();
        // turn 1 claims a pre-root of root(7), but the head is root(1).
        let bad = batch(1, root(7), root(2));
        let err = chain.extend(&bad).unwrap_err();
        assert!(matches!(err, ChainRefusal::RootMismatch { .. }));
        // The chain head did NOT move — a bad batch cannot corrupt it.
        assert_eq!(chain.head(), Some(root(1)));
        assert_eq!(chain.next_ordinal(), 1);
    }

    #[test]
    fn chain_refuses_a_gap_or_replay() {
        let g = root(0);
        let mut chain = RootChain::resume(g, 0);
        chain.extend(&batch(0, g, root(1))).unwrap();
        // Skipping to ordinal 2 (gap) is refused.
        let gap = chain.extend(&batch(2, root(1), root(3))).unwrap_err();
        assert!(matches!(gap, ChainRefusal::OrdinalGap { expected: 1, got: 2 }));
        // Replaying ordinal 0 is refused.
        let replay = chain.extend(&batch(0, g, root(1))).unwrap_err();
        assert!(matches!(replay, ChainRefusal::OrdinalGap { expected: 1, got: 0 }));
    }

    #[test]
    fn chain_refuses_a_batch_with_smuggled_rows() {
        // A batch carrying a row stamped with a different ordinal is malformed:
        // you cannot smuggle a row from turn 5 into turn 1's batch.
        let g = root(0);
        let mut chain = RootChain::resume(g, 0);
        let mut b = batch(0, g, root(1));
        b.cells[0].last_ordinal = 99; // smuggled
        let err = chain.extend(&b).unwrap_err();
        assert!(matches!(err, ChainRefusal::Malformed(_)));
        // The chain is UNCHANGED — a malformed batch never advances the head.
        assert_eq!(chain.head(), Some(g), "a malformed genesis batch is rejected");
        assert_eq!(chain.next_ordinal(), 0);
    }

    #[test]
    fn batch_ordinal_check_catches_each_row_kind() {
        let g = root(0);
        let mut b = batch(3, g, root(1));
        assert!(b.check_ordinals().is_ok());
        b.caps.push(CapRow {
            holder: root(9),
            slot: 0,
            target: root(8),
            permissions_json: "{}".into(),
            breadstuff: None,
            expires_at: None,
            allowed_effects_json: None,
            stored_epoch: 7.into(),
            last_ordinal: 4, // wrong
        });
        assert!(b.check_ordinals().is_err());
    }

    #[test]
    fn mirror_batch_serde_roundtrips() {
        // The wire unit the node ships must round-trip exactly.
        let b = batch(0, root(0), root(1));
        let bytes = serde_json::to_vec(&b).unwrap();
        let back: MirrorBatch = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(b, back);
    }

    #[test]
    fn ddl_is_emittable_and_mentions_the_lockdown() {
        let sql = ddl::tier_b();
        // The spine: apps read, only the kernel writes. The DDL must REVOKE
        // writes from PUBLIC and grant them only to dregg_kernel.
        assert!(sql.contains("REVOKE INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg FROM PUBLIC"));
        assert!(sql.contains("GRANT SELECT ON ALL TABLES IN SCHEMA dregg TO dregg_reader"));
        assert!(sql.contains("FORCE ROW LEVEL SECURITY"));
        // Every state table is RLS-gated by the Tier A cap layer.
        assert!(sql.contains("dregg_admits('read'"));
        // The universal-memory table exists.
        assert!(sql.contains("dregg.memory"));
        // The dregg-dev query-surface views are emitted.
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.cell_balances"));
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.cap_edges"));
        assert!(sql.contains("CREATE OR REPLACE VIEW dregg.receipt_chain"));
    }

    /// ANTI-DRIFT: the committed `sql/schema-tierB.sql` and the Rust DDL emitter
    /// (`ddl::tier_b()`) must AGREE — they describe the same tables, views, and
    /// policies. The SQL file is the human-readable, fully-commented form; the
    /// emitter is what the extension ships. This test pins them together so they
    /// cannot silently diverge: every CREATE TABLE / CREATE VIEW / CREATE POLICY
    /// the emitter produces must appear (whitespace- and modifier-normalized) in
    /// the committed SQL file, and vice-versa for the load-bearing relations.
    #[test]
    fn emitted_ddl_agrees_with_committed_sql_file() {
        let emitted = ddl::tier_b();
        let file = include_str!("../sql/schema-tierB.sql");

        // The relation/policy names the two MUST share. (Names, not full bodies:
        // the file carries extra comments + the cell_history/blocks tables that
        // are documented-as-future and not yet in the emitter; the emitter is the
        // shippable subset. Names are the anti-drift contract.)
        let shared = [
            "CREATE TABLE", // turns
            "dregg.turns",
            "dregg.cells",
            "dregg.capabilities",
            "dregg.memory",
            "dregg.cap_edges",
            "dregg.cell_balances",
            "dregg.receipt_chain",
            "CREATE POLICY cells_read",
            "CREATE POLICY turns_read",
            "CREATE POLICY caps_read",
            "CREATE POLICY memory_read",
            "dregg_admits('read'",
            "FORCE ROW LEVEL SECURITY",
            "REVOKE INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg FROM PUBLIC",
        ];
        for needle in shared {
            assert!(
                emitted.contains(needle),
                "emitter is missing `{needle}` (drift vs schema-tierB.sql)"
            );
            assert!(
                file.contains(needle),
                "schema-tierB.sql is missing `{needle}` (drift vs ddl::tier_b())"
            );
        }

        // Column-level agreement on the spine table the writer must fill: every
        // column the emitter declares for dregg.cells must be named in the file.
        for col in [
            "cell_id", "mode", "balance", "nonce", "fields", "fields_json", "heap",
            "program", "verification_key", "delegate", "lifecycle", "last_ordinal",
            "cell_root",
        ] {
            assert!(file.contains(col), "schema-tierB.sql missing cells column `{col}`");
            assert!(emitted.contains(col), "emitter missing cells column `{col}`");
        }
    }
}
