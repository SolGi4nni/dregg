-- pg-dregg — worked RLS examples (Milestone 1; see docs/PG-DREGG.md §2.2).
--
-- The functions are provided by the pg-dregg extension, backed by dregg-auth's
-- proven credential core. A token reaches every policy via the `dregg.token`
-- session GUC; prefer transaction-local set_config(..., true) on pooled
-- connections so the bearer token clears at transaction end.
--
-- These statements are illustrative (they assume the tables exist and the
-- extension is installed); the machine-checked proofs of the same behaviour are
-- the #[pg_test]s in src/lib.rs (run by `cargo pgrx test pg14`) and the
-- postgres-independent core tests in src/authz.rs (run by `cargo test`).
--
-- TWO QUICKSTARTS walk these end-to-end:
--   * docs/QUICKSTART-pg-user.md   — a plain table → cap-gated RLS in ~10 min.
--   * docs/QUICKSTART-dregg-dev.md — postgres as the dregg store/query surface.
-- and `cargo run --example end_to_end` runs the whole arc (mirror → root-chain →
-- DDL → RLS-narrowing + anti-substitution + revocation) on synthetic turns.

-- ---------------------------------------------------------------------------
-- 0. Install + the trust root.
-- ---------------------------------------------------------------------------
CREATE EXTENSION IF NOT EXISTS pg_dregg;

-- The database trust root: the issuer PUBLIC key (publishable; the private key
-- never enters postgres). The GUC is Sighup — set it in postgresql.conf or with
-- ALTER SYSTEM + reload, NOT a session SET (so a session cannot point
-- verification at a key it controls).
--   # postgresql.conf
--   dregg.issuer_pubkey = 'b3f1…<64 hex>'
-- or
--   ALTER SYSTEM SET dregg.issuer_pubkey = 'b3f1…<64 hex>';
--   SELECT pg_reload_conf();

-- ---------------------------------------------------------------------------
-- 1. A documents table gated by dregg capabilities instead of a hand-rolled
--    tenant predicate.
-- ---------------------------------------------------------------------------
CREATE TABLE documents (id text PRIMARY KEY, body text);

ALTER TABLE documents ENABLE ROW LEVEL SECURITY;
-- FORCE so even the table owner is subject to the policy. (Note: a postgres
-- SUPERUSER still BYPASSES RLS entirely — gate your app behind a non-superuser,
-- non-BYPASSRLS role.)
ALTER TABLE documents FORCE ROW LEVEL SECURITY;

-- READ: a token must admit `read` on this row's id (or a prefix covering it).
CREATE POLICY cap_read ON documents
  FOR SELECT
  USING (dregg_admits('read', id::text));
-- Equivalent explicit form (what dregg_admits expands to):
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

-- ---------------------------------------------------------------------------
-- 2. Presenting a token for the session (transaction-local on a pool):
-- ---------------------------------------------------------------------------
--   SELECT set_config('dregg.token', 'dga1_…', true);
--   SELECT * FROM documents;          -- returns only the admitted rows
--
-- An attenuated token (narrowed to a resource prefix) sees a STRICT SUBSET of
-- what its parent saw — the no-amplify property, enforced inside dregg-auth and
-- proven through this boundary by the attenuation #[pg_test].

-- ---------------------------------------------------------------------------
-- 3. Instant revocation (ember decision #1 — the DEFAULT path, not TTL).
-- ---------------------------------------------------------------------------
-- Every policy evaluation also consults the revocation registry, so a revoked
-- credential is denied on the very NEXT row-check (not after a TTL). Revoke the
-- exact presented credential by its stable id:
--   SELECT dregg_revoke(current_setting('dregg.token', true));   -- returns the id
-- After this, the same SELECT returns zero of that credential's rows. Lift it:
--   SELECT dregg_unrevoke('<id>');
-- The id keyed on is the credential's chain-committing tail:
--   SELECT dregg_cap_id(current_setting('dregg.token', true));

-- ---------------------------------------------------------------------------
-- 4. Why a row was filtered (debugging) — the explain discipline.
-- ---------------------------------------------------------------------------
--   SELECT id, dregg_cap_explain(current_setting('dregg.token', true),
--                                'read', id::text,
--                                extract(epoch from now())::bigint)
--   FROM documents;
-- and the confined subject the token names (for actor-column joins / audit):
--   SELECT dregg_cap_subject(current_setting('dregg.token', true));
