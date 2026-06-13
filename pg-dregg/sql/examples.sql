-- pg-dregg — worked RLS examples (SKELETON; see docs/PG-DREGG.md §2.2).
-- Functions are provided by the pg-dregg extension, backed by dregg-auth's
-- proven credential core. The token reaches every policy via the dregg.token
-- session GUC; prefer transaction-local set_config(..., true) on pooled
-- connections so the bearer token clears at transaction end.

-- The database's trust root: the issuer PUBLIC key (publishable).
-- (Set in postgresql.conf or per-database.)
--   ALTER DATABASE app SET dregg.issuer_pubkey = 'b3f1…<64 hex>';

-- A documents table gated by dregg capabilities instead of a hand-rolled
-- tenant predicate.
ALTER TABLE documents ENABLE ROW LEVEL SECURITY;

-- READ: a token must admit `read` on this row's id (or a prefix covering it).
CREATE POLICY cap_read ON documents
  FOR SELECT
  USING (dregg_admits('read', id::text));
-- Equivalent explicit form:
--   USING (dregg_cap_admits(
--     current_setting('dregg.token', true),
--     'read', id::text, extract(epoch from now())::bigint));

-- WRITE (UPDATE): the targeted rows AND the post-image must both be admitted.
CREATE POLICY cap_update ON documents
  FOR UPDATE
  USING      (dregg_admits('write', id::text))
  WITH CHECK (dregg_admits('write', id::text));

-- INSERT: the produced row must be admitted.
CREATE POLICY cap_insert ON documents
  FOR INSERT
  WITH CHECK (dregg_admits('create', id::text));

-- DELETE.
CREATE POLICY cap_delete ON documents
  FOR DELETE
  USING (dregg_admits('delete', id::text));

-- Presenting a token for the session (transaction-local on a pool):
--   SELECT set_config('dregg.token', 'dga1_…', true);
--   SELECT * FROM documents;          -- returns only the admitted rows
--
-- Why a row was filtered (debugging):
--   SELECT id, dregg_cap_explain(current_setting('dregg.token', true),
--                                'read', id::text,
--                                extract(epoch from now())::bigint)
--   FROM documents;
