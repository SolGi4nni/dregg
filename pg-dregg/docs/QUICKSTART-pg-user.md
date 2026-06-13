# pg-dregg quickstart — for the postgres user

You live in postgres. Your authorization is hand-rolled RLS predicates over a
JWT, or app-tier checks the database trusts blindly. `pg-dregg` replaces that
policy substrate with dregg's **verified object-capability tokens**: one signed,
attenuable, offline-verifiable token gates your rows — and the same token works
against the dregg kernel if you ever talk to one.

You learn exactly one new thing: a token string. Everything else is `CREATE
POLICY` you already know.

This is the ~10-minute path from a plain table to cap-gated RLS. Every command
is real and is exercised by the `#[pg_test]`s in `src/lib.rs` (run against real
pg14) and the core tests in `src/authz.rs`.

---

## 0. Install the extension and set the trust root

```bash
# Build + install into a pg14 you manage (cargo-pgrx 0.17 + a pg14 from
# `cargo pgrx init --pg14 ...`).
cd pg-dregg
cargo pgrx install --pg-config $(which pg_config)
```

```sql
CREATE EXTENSION pg_dregg;
```

The database's trust root is the issuer **public** key (publishable; the private
key never enters postgres). It is a `Sighup` GUC — set it in `postgresql.conf`
or with `ALTER SYSTEM`, **never** a session `SET` (so a session cannot point
verification at a key it controls and forge access):

```conf
# postgresql.conf
dregg.issuer_pubkey = 'ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c'
```

```sql
-- or, then reload:
ALTER SYSTEM SET dregg.issuer_pubkey = 'ea4a6c63…';
SELECT pg_reload_conf();
```

A malformed or absent key makes **every** `dregg_cap_admits` return FALSE
(fail-closed). Nothing is open by default.

---

## 1. Gate a plain table with a capability policy

Take any table:

```sql
CREATE TABLE documents (id text PRIMARY KEY, body text);
INSERT INTO documents VALUES
  ('org/42/public/doc1', '…'),
  ('org/42/public/doc2', '…'),
  ('org/42/private/doc9', '…'),
  ('org/99/public/doc1', '…');
```

Turn on RLS and write the policy in terms of a **capability decision** instead
of a hand-rolled predicate:

```sql
ALTER TABLE documents ENABLE ROW LEVEL SECURITY;
ALTER TABLE documents FORCE ROW LEVEL SECURITY;   -- even the owner is filtered

-- A reader sees a row iff their presented token admits `read` on that row's id.
CREATE POLICY cap_read ON documents
  FOR SELECT
  USING (dregg_admits('read', id::text));
```

`dregg_admits(action, resource)` reads the session's token from
`current_setting('dregg.token', true)` and the clock from `now()`, then asks
dregg-auth whether the token admits `action` on `resource`. The explicit form it
expands to:

```sql
USING (dregg_cap_admits(
  current_setting('dregg.token', true),
  'read', id::text, extract(epoch from now())::bigint));
```

> **Important:** a postgres **superuser** BYPASSES RLS entirely. Run your app
> behind a non-superuser, non-`BYPASSRLS` role, or the policy never fires.

---

## 2. Present a token; watch the rows narrow

A token is a `dga1_…` string your issuer minted. Present it for the session
(prefer transaction-local on a pooled connection so it clears at commit):

```sql
SELECT set_config('dregg.token', 'dga1_…the-root-token…', true);
SELECT id FROM documents;
--  org/42/public/doc1
--  org/42/public/doc2
--  org/42/private/doc9      ← a token scoped to org/42/ sees all three
```

Now present an **attenuated** token — one a delegate holds, narrowed to
`org/42/public/` only. You did not change the policy or the data; you changed
the authority presented:

```sql
SELECT set_config('dregg.token', 'dga1_…attenuated-to-public…', true);
SELECT id FROM documents;
--  org/42/public/doc1
--  org/42/public/doc2       ← the private doc VANISHED — strict subset
```

This is the **no-amplification** property, enforced inside dregg-auth and proven
through the SQL boundary by `admits_and_attenuation_narrows_through_sql` and
`rls_gated_table_narrows_row_visibility` (`cargo pgrx test pg14`). The child
token can only ever see a subset of what its grantor saw — something a flat JWT
claim in a GUC structurally cannot guarantee.

---

## 3. Write policies too

The same decision gates writes; `WITH CHECK` enforces the post-image is also
admitted:

```sql
CREATE POLICY cap_update ON documents FOR UPDATE
  USING      (dregg_admits('write', id::text))
  WITH CHECK (dregg_admits('write', id::text));

CREATE POLICY cap_insert ON documents FOR INSERT
  WITH CHECK (dregg_admits('create', id::text));

CREATE POLICY cap_delete ON documents FOR DELETE
  USING (dregg_admits('delete', id::text));
```

---

## 4. Instant revocation

Revocation is the default path, not a TTL wait. Every policy evaluation also
consults the revocation registry, so a revoked credential is denied on the very
**next** row-check:

```sql
SELECT dregg_revoke(current_setting('dregg.token', true));   -- returns the id
-- the same SELECT now returns ZERO of that credential's rows.
SELECT dregg_unrevoke('<id>');                                -- lift it
```

The id keyed on is the credential's chain-committing tail:

```sql
SELECT dregg_cap_id(current_setting('dregg.token', true));
```

Proven by `instant_revocation_makes_rows_vanish` (`cargo pgrx test pg14`).

---

## 5. Why a row was filtered (debugging)

A row that fails `USING` simply disappears — miserable to debug. dregg names the
violated requirement:

```sql
SELECT id, dregg_cap_explain(current_setting('dregg.token', true),
                             'read', id::text,
                             extract(epoch from now())::bigint)
FROM documents;
-- 'allowed', or e.g. 'attribute `resource` has prefix `org/42/public/`' (the
-- first violated caveat), or 'revoked', or 'no issuer key configured'.
```

And the confined subject a token names (for actor-column joins / audit):

```sql
SELECT dregg_cap_subject(current_setting('dregg.token', true));   -- e.g. 'agent-1'
```

---

## What you got

| You wanted | Hand-rolled RLS | pg-dregg |
|---|---|---|
| delegation (hand a sub-agent less, offline) | role DDL, central | attenuate a token, no round-trip |
| provable narrowing (child ⊆ grantor) | inexpressible | the no-amplify property, enforced |
| time-boxing | thread an `expires_at` column | `NotAfter` caveat on the token |
| per-credential revocation | `DROP POLICY`, coarse | `dregg_revoke`, instant, per-token |
| explainable denial | the row just vanishes | `dregg_cap_explain` names the reason |

You added one extension, one GUC, and policies in a closed, proved capability
calculus. The full SQL surface and the assurance boundary are in
`docs/PG-DREGG.md`; the dregg-developer view (postgres as the dregg store) is in
`QUICKSTART-dregg-dev.md`.
