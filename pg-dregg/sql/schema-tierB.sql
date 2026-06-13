-- pg-dregg — Tier B schema sketch: dregg state AS queryable postgres tables.
--
-- =============================================================================
-- ⚠ DESIGN SKETCH — NOT A MIGRATION. See docs/PG-DREGG.md §8 (Tier B/C/D).
-- =============================================================================
-- This file is the concrete artifact for the Tier B proposal: it shows the
-- shape of the cells / receipts / blocklace / capability tables, the
-- universal-memory single table, and the RLS policies that compose with the
-- LANDED M1 authz layer (dregg_admits / dregg_cap_admits, see src/authz.rs).
--
-- The Rust mirror core (src/mirror.rs) is the postgres-free, cargo-test-proven
-- backbone of this schema: it owns the row types, the universal-memory Domain
-- model, the DDL emitter (`mirror::ddl::tier_b()` regenerates these tables), and
-- the RootChain anti-substitution tooth. Tier C (the verify gate) is the sibling
-- file schema-tierC.sql.
--
-- THE LOAD-BEARING INVARIANT (the spine of the whole design):
--
--     Reads are free SQL; state mutates ONLY through verified turns.
--
-- Every table below is a MATERIALIZED VIEW of state the dregg kernel produced.
-- A row appears here ONLY as the post-image of a verified turn (the commit
-- log's CommitRecord — persist/src/commit_log.rs). Ordinary `SELECT` queries
-- this freely. A bare SQL `INSERT/UPDATE/DELETE` by an application role is
-- FORBIDDEN — it would bypass the executor and break conservation /
-- no-amplification / nullifier-uniqueness. Tier C (the dregg_verify_turn CHECK
-- tooth, §9) is what mechanically enforces that forbiddance; this file sets up
-- the tables and the read-side RLS, and marks the write-lockdown that Tier C
-- fills in.
--
-- Provenance of every column is named against the real Rust types so the
-- mirror is a faithful projection, not an invention:
--   * persist/src/commit_log.rs  :: CommitRecord
--   * persist/src/ledger_store.rs :: LedgerCheckpoint
--   * cell/src/cell.rs            :: Cell / CellState / Permissions
--   * cell/src/capability.rs      :: CapabilitySet / CapabilityRef
--   * docs/UNIVERSAL-MEMORY.md    :: the (domain,key)->value Blum multiset

CREATE EXTENSION IF NOT EXISTS pg_dregg;
CREATE SCHEMA IF NOT EXISTS dregg;

-- ===========================================================================
-- 0.  The write-lockdown role model (Tier C precondition).
-- ===========================================================================
-- Two roles, sharply separated:
--   * dregg_kernel  — the ONLY role permitted to INSERT/UPDATE dregg.* state.
--                     In Tier C/D this is the role the verifier/executor
--                     function runs as (SECURITY DEFINER). NOTHING ELSE writes.
--   * dregg_reader  — applications. SELECT only. RLS-gated by the M1 caps.
-- A bare application connection is dregg_reader: it can never mutate state.
CREATE ROLE dregg_kernel  NOLOGIN;   -- the verified writer (SECURITY DEFINER target)
CREATE ROLE dregg_reader  NOLOGIN;   -- applications: reads only

-- ===========================================================================
-- 1.  RECEIPTS / TURNS — the spine. A direct projection of CommitRecord.
-- ===========================================================================
-- This table is the authority for "what verified turns happened". Every other
-- state table (cells, memory, caps) is reconcilable to it: a cell row at
-- ordinal N is the touched_cells post-image of the turn at ordinal N.
CREATE TABLE dregg.turns (
    ordinal              bigint PRIMARY KEY,            -- CommitRecord.ordinal (dense, gap-free)
    height               bigint NOT NULL,               -- CommitRecord.height (attested-root height)
    block_id             bytea  NOT NULL,               -- CommitRecord.block_id (consensus anchor)
    block_executed_up_to bigint NOT NULL,               -- CommitRecord.block_executed_up_to
    turn_hash            bytea  NOT NULL UNIQUE,         -- CommitRecord.turn_hash
    creator              bytea  NOT NULL,               -- CommitRecord.creator (agent CellId)
    receipt_hash         bytea  NOT NULL,               -- CommitRecord.receipt_hash
    ledger_root          bytea  NOT NULL,               -- CommitRecord.ledger_root (post-state commitment)
    committed_at         timestamptz NOT NULL DEFAULT now()  -- wall-clock mirror time (NOT consensus time)
);
CREATE INDEX turns_by_height  ON dregg.turns (height);
CREATE INDEX turns_by_creator ON dregg.turns (creator, ordinal);
-- The mirror's own integrity tooth: ordinals are dense. (Tier C strengthens
-- this to "ledger_root chains": each row's ledger_root is the verified
-- post-state of applying turn_hash to the prior row's ledger_root.)

-- ===========================================================================
-- 2.  CELLS — the live ledger, one row per cell, AS OF the latest turn.
-- ===========================================================================
-- A projection of dregg_cell::Cell (cell/src/cell.rs) + LedgerCheckpoint.cells.
-- `last_ordinal` ties each cell row to the turn that produced its post-image,
-- so a join `cells ⋈ turns ON last_ordinal = ordinal` is fully reconcilable.
CREATE TABLE dregg.cells (
    cell_id        bytea PRIMARY KEY,         -- Cell.id() (CellId, 32 bytes)
    mode           text  NOT NULL,            -- CellMode (Hosted | Sovereign | ...)
    balance        bigint NOT NULL,           -- CellState balance
    nonce          bigint NOT NULL,           -- CellState nonce (monotone)
    -- State payload kept BOTH as raw bytes (faithful) and as jsonb (queryable).
    -- The bytea is canonical; the jsonb is a decoded convenience the mirror
    -- writer fills. Queries use jsonb; integrity reconciles on bytea.
    fields         bytea NOT NULL,            -- CellState.fields (FieldElement slots), canonical
    fields_json    jsonb,                     -- decoded slot array, for `fields_json->>'0'` queries
    heap           bytea,                     -- CellState heap (openable sorted map), canonical
    program        bytea,                     -- CellProgram (predicate / verification key bound)
    verification_key bytea,                   -- Cell.verification_key (Option)
    permissions    jsonb,                     -- Cell.permissions (Permissions), decoded
    delegate       bytea,                     -- Cell.delegate (Option<CellId>)
    lifecycle      text  NOT NULL,            -- CellLifecycle (Active | Sealed | ...)
    last_ordinal   bigint NOT NULL REFERENCES dregg.turns(ordinal),  -- the turn that produced this row
    cell_root      bytea NOT NULL             -- this cell's commitment (recStateCommit); part of ledger_root
);
CREATE INDEX cells_by_balance  ON dregg.cells (balance);
CREATE INDEX cells_by_mode     ON dregg.cells (mode);
CREATE INDEX cells_fields_gin  ON dregg.cells USING gin (fields_json);
CREATE INDEX cells_perms_gin   ON dregg.cells USING gin (permissions);

-- Optional: full history (every post-image, not just latest) for time-travel.
-- This is the cell-by-(id,ordinal) index of the commit log, surfaced as SQL.
CREATE TABLE dregg.cell_history (
    cell_id     bytea  NOT NULL,
    ordinal     bigint NOT NULL REFERENCES dregg.turns(ordinal),
    balance     bigint NOT NULL,
    nonce       bigint NOT NULL,
    fields_json jsonb,
    cell_root   bytea  NOT NULL,
    PRIMARY KEY (cell_id, ordinal)
);
CREATE INDEX cell_history_by_ordinal ON dregg.cell_history (ordinal);

-- ===========================================================================
-- 3.  CAPABILITIES + the delegation graph (cell/src/capability.rs).
-- ===========================================================================
-- One row per CapabilityRef in a cell's CapabilitySet. (holder, slot) is the
-- c-list address; `target` is the cell the capability reaches. The graph is
-- holder -> target edges; recursive queries walk the delegation tree.
CREATE TABLE dregg.capabilities (
    holder       bytea  NOT NULL REFERENCES dregg.cells(cell_id),  -- the cell that HOLDS the cap
    slot         int    NOT NULL,                                  -- CapabilityRef.slot (c-list position)
    target       bytea  NOT NULL,                                  -- CapabilityRef.target (cell reached)
    permissions  jsonb  NOT NULL,                                  -- CapabilityRef.permissions (AuthRequired)
    breadstuff   bytea,                                            -- CapabilityRef.breadstuff (token hash)
    expires_at   bigint,                                           -- CapabilityRef.expires_at (Option<height>)
    allowed_effects jsonb,                                         -- CapabilityRef.allowed_effects (attenuation)
    stored_epoch bigint,                                           -- CapabilityRef.stored_epoch (group-key epoch)
    last_ordinal bigint NOT NULL REFERENCES dregg.turns(ordinal),
    PRIMARY KEY (holder, slot)
);
CREATE INDEX caps_by_target ON dregg.capabilities (target);
-- The delegation graph as a view; WITH RECURSIVE over it gives reachability /
-- the no-amplification audit (a child's allowed_effects ⊆ its grantor's).
CREATE VIEW dregg.cap_edges AS
    SELECT holder AS src, target AS dst, slot, permissions, expires_at
    FROM dregg.capabilities;

-- ===========================================================================
-- 4.  BLOCKLACE DAG (persist/src/blocklace_store.rs) — the consensus layer.
-- ===========================================================================
CREATE TABLE dregg.blocks (
    block_id   bytea PRIMARY KEY,        -- block hash
    creator    bytea NOT NULL,           -- block creator (validator CellId)
    seq        bigint NOT NULL,          -- creator-local sequence number
    payload_kind text NOT NULL,          -- 'turn' | 'heartbeat' | 'membership' | 'checkpoint'
    turn_ordinal bigint REFERENCES dregg.turns(ordinal)  -- the turn this block carried, if any
);
-- The DAG edges (a block ACKNOWLEDGES its predecessors — the blocklace pointers).
CREATE TABLE dregg.block_edges (
    child  bytea NOT NULL REFERENCES dregg.blocks(block_id),  -- the acknowledging block
    parent bytea NOT NULL REFERENCES dregg.blocks(block_id),  -- the acknowledged predecessor
    PRIMARY KEY (child, parent)
);
CREATE INDEX block_edges_parent ON dregg.block_edges (parent);

-- ===========================================================================
-- 5.  UNIVERSAL MEMORY — the elegant collapse (docs/UNIVERSAL-MEMORY.md).
-- ===========================================================================
-- The Blum multiset over Domain × κ maps to ONE table. Domain ∈ {registers,
-- heap, caps, nullifiers, index}; a future state component is a NEW DOMAIN
-- VALUE, never a new table — so this single relation is the whole memory.
-- (Tables 2-4 above are then DERIVED BOUNDARY VIEWS over this one table, exactly
-- as the four map roots are derived boundary views over the final memory cells.
-- Whether to keep tables 2-4 as real tables or as VIEWS over dregg.memory is an
-- ember decision, §8: the typed tables are nicer to query; the single table is
-- the honest model.)
CREATE TABLE dregg.memory (
    domain       text  NOT NULL,         -- 'registers'|'heap'|'caps'|'nullifiers'|'index'
    collection   bytea NOT NULL,         -- collection_id (e.g. the cell, the map)
    key          bytea NOT NULL,         -- κ within the domain
    value        bytea,                  -- Option ν: NULL = absent cell, non-null = present
    last_ordinal bigint NOT NULL REFERENCES dregg.turns(ordinal),
    PRIMARY KEY (domain, collection, key)
);
CREATE INDEX memory_by_domain ON dregg.memory (domain);
-- The boundary roots (cap_root / nullifier_root / heap_root / index root) are
-- `SELECT dregg_domain_root('caps', collection)` over the present cells — a
-- derived view, matching boundary_root_derived. Equality of that derived root
-- with the committed map root is the Lean-proved boundary reconciliation.

-- ===========================================================================
-- 6.  READ-SIDE RLS — every state table composes with the M1 cap layer.
-- ===========================================================================
-- The reader sees ONLY the cells/turns/caps its presented dregg token admits.
-- This is the M1 dregg_admits gate (src/authz.rs) applied to the mirror: the
-- explorer is "your capabilities, expressed as the rows you may SELECT".
ALTER TABLE dregg.cells        ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.turns        ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.capabilities ENABLE ROW LEVEL SECURITY;
ALTER TABLE dregg.memory       ENABLE ROW LEVEL SECURITY;

-- A token admits a cell row iff it admits `read` on that cell id.
CREATE POLICY cells_read ON dregg.cells FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(cell_id, 'hex')));

-- A token admits a turn row iff it admits `read` on the turn's creator cell
-- (you can see the turns of agents you can read). Public-explorer deployments
-- relax this to USING (true) for the turns table while keeping cells gated.
CREATE POLICY turns_read ON dregg.turns FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(creator, 'hex')));

CREATE POLICY caps_read ON dregg.capabilities FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(holder, 'hex')));

CREATE POLICY memory_read ON dregg.memory FOR SELECT TO dregg_reader
    USING (dregg_admits('read', encode(collection, 'hex')));

-- ===========================================================================
-- 7.  WRITE LOCKDOWN — the spine, mechanically (Tier C fills the CHECK).
-- ===========================================================================
-- Applications (dregg_reader) get SELECT only. NO write grants. The ONLY writer
-- is dregg_kernel, and in Tier C even dregg_kernel's writes pass through the
-- dregg_verify_turn CHECK (see docs/PG-DREGG.md §9 and schema-tierC.sql).
GRANT USAGE  ON SCHEMA dregg TO dregg_reader, dregg_kernel;
GRANT SELECT ON ALL TABLES IN SCHEMA dregg TO dregg_reader;
GRANT INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg TO dregg_kernel;

-- Belt-and-braces: FORCE RLS so even the table owner is filtered, and REVOKE
-- any default write from PUBLIC. A bare SQL INSERT by an app is rejected at the
-- privilege layer BEFORE any trigger; Tier C's trigger then guarantees that
-- even dregg_kernel cannot write a row that is not a verified-turn post-image.
ALTER TABLE dregg.cells        FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.turns        FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.capabilities FORCE ROW LEVEL SECURITY;
ALTER TABLE dregg.memory       FORCE ROW LEVEL SECURITY;
REVOKE INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA dregg FROM PUBLIC;

-- ===========================================================================
-- 8.  Worked queries — the payoff. The explorer, expressed as SQL.
-- ===========================================================================
-- (illustrative; each is RLS-gated by §6, so it returns only admitted rows.)

-- Richest cells you can see:
--   SELECT encode(cell_id,'hex'), balance FROM dregg.cells ORDER BY balance DESC LIMIT 10;

-- Conservation check over a turn (sum of touched-cell balances unchanged):
--   SELECT t.ordinal, sum(ch.balance) FROM dregg.cell_history ch
--   JOIN dregg.turns t ON t.ordinal = ch.ordinal GROUP BY t.ordinal;

-- The delegation tree rooted at one cell (no-amplification audit surface):
--   WITH RECURSIVE reach(src,dst,depth) AS (
--     SELECT src,dst,1 FROM dregg.cap_edges WHERE src = $root
--     UNION ALL
--     SELECT e.src,e.dst,r.depth+1 FROM dregg.cap_edges e
--     JOIN reach r ON e.src = r.dst WHERE r.depth < 32)
--   SELECT * FROM reach;

-- Turns by an agent, newest first, joined to their post-state root:
--   SELECT ordinal, height, encode(ledger_root,'hex')
--   FROM dregg.turns WHERE creator = $agent ORDER BY ordinal DESC;
