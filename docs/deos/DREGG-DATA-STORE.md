# DREGG-DATA-STORE — deos's cap-secured, orthogonal-persistence database

A deos app — especially the builders-dev SaaS — gets storage where **every row
is gated by the same kernel capability decision**. The store is a self-contained
bundle: a bleeding-edge **PostgreSQL 18** + the **pg-dregg** extension
(capabilities as Row-Level Security) + the **dregg-query** read face (attested
conjunctive queries that cannot silently omit rows). One token authorizes
against the dregg kernel AND against your plain tables; a row you cannot
cap-reach is invisible, and a query over what you can reach cannot hide rows.

This document is the vision, the bundle model, the trust story, and the
builders-dev adoption path. It is written in present tense from first
principles; the runnable first slice lives in
`pg-dregg/tests/cap_secured_store.rs` (the RLS row-filter) and
`dregg-query/tests/cap_secured_read.rs` (the attested read). The substrate it
builds on is documented in `docs/design-frontiers/PG-DREGG-DX.md` (the extension)
and the `dregg-query/` crate (the query surface).

---

## 1. The vision: orthogonal persistence, cap-gated

The Houyhnhnm ideal deos reaches for is **orthogonal persistence**: the source
is the semantic state — there is no separate "save format", no impedance
mismatch between the running image and what is on disk. A cell's state simply
*is* persisted, and the kernel's authority decision over that state is the same
whether the state is live in memory or sitting in a table.

A conventional database breaks this. Authority over rows lives in a *second*
place — hand-rolled RLS predicates (`tenant_id = current_setting('app.tenant')`),
application-layer checks, ORM scopes — that must be kept in sync with whatever
the application *means* by "who may see this". Every place that authority is
re-expressed is a place it can drift, and every drift is a leak.

The cap-secured store collapses the two places into one. The authority over a
row is a dregg capability — the exact same object the kernel exercises when an
agent takes a turn. There is no second predicate to keep in sync: the row's
gate IS the kernel decision. This is what makes the store orthogonal-persistence
*grade*: the persisted state and the authority over it are governed by one
mechanism, not two.

---

## 2. The bundle: PG18 + pg-dregg + dregg-query

deos ships the store as a self-contained unit:

```
┌──────────────────────────────────────────────────────────────┐
│  deos cap-secured data store (one bundle)                      │
│                                                                │
│  ┌────────────────────────────────────────────────────────┐  │
│  │  PostgreSQL 18                                           │  │
│  │   • dregg.issuer_pubkey GUC  — the database trust root   │  │
│  │   • pg-dregg extension auto-loaded (shared_preload)      │  │
│  │       dregg_admits(action, resource) -> bool            │  │
│  │       dregg_cap_admits(token, action, resource, now)    │  │
│  │   • app tables with RLS USING (dregg_admits(...))        │  │
│  └────────────────────────────────────────────────────────┘  │
│                          ▲                                     │
│        the SAME dga1_ token                                    │
│                          ▼                                     │
│  ┌────────────────────────────────────────────────────────┐  │
│  │  dregg-query  — the attested READ face                   │  │
│  │   • conjunctive queries over the receipt fact-base       │  │
│  │   • CALM grade (monotone vs finalized-dependent)        │  │
│  │   • non-omission certificate (range proof: no hidden row)│  │
│  └────────────────────────────────────────────────────────┘  │
└──────────────────────────────────────────────────────────────┘
```

**PostgreSQL 18** is the storage engine. pg18 is chosen deliberately: virtual
generated columns, `RETURNING old/new`, uuidv7, OAuth, async I/O, and the
`CHECK ... NOT ENFORCED` / `NOT NULL ... NOT VALID` constraint forms pg-dregg
already uses (`docs/design-frontiers/PG-DREGG-DX.md` Tier B). The bundle preloads the pg-dregg
extension (`shared_preload_libraries = 'pg_dregg'`) and configures the issuer
public key once (`dregg.issuer_pubkey`), which is the database's trust root.

**pg-dregg** is the gate. Its postgres-free CORE (`pg-dregg/src/authz.rs`) makes
the capability decision; its `#[pg_extern]` wrappers (`pg-dregg/src/lib.rs`,
gated behind the `pgrx` feature) marshal SQL into that decision. The
load-bearing function is `dregg_admits(action, resource)` — it reads the
session's `dregg.token` GUC and `now()`, then calls
`authz::decide(token, action, resource, now)`. That is the EXACT decision the
kernel makes from the same token.

**dregg-query** is the read face. A query over the receipt fact-base returns
rows plus a certificate that the answer was computed from exactly the committed
receipt range — nothing hidden, nothing forged, nothing reordered.

### Declaring a cap-gated table

A deos app declares an ordinary table with one extra column — the per-row
capability id the gate checks — and one RLS policy:

```sql
-- the application's own table, with a row_cap column
CREATE TABLE app.documents (
    id        uuid PRIMARY KEY DEFAULT uuidv7(),
    row_cap   bytea NOT NULL,          -- the per-row resource id the cap names
    body      jsonb NOT NULL
);
ALTER TABLE app.documents ENABLE ROW LEVEL SECURITY;

-- the ONE policy: a row is visible iff the kernel decision admits 'read' on it
CREATE POLICY documents_read ON app.documents FOR SELECT TO app_role
    USING (dregg_admits('read', encode(row_cap, 'hex')));

CREATE POLICY documents_write ON app.documents FOR INSERT TO app_role
    WITH CHECK (dregg_admits('write', encode(row_cap, 'hex')));
```

The application presents its capability once per session:

```sql
SET dregg.token = 'dga1_…';     -- or the pg18 login event trigger binds it
SELECT * FROM app.documents;    -- returns ONLY the cap-reachable rows
```

That is the whole integration. No `tenant_id` column to filter on, no
application-layer scope check, no ORM predicate. The row's gate is the kernel
decision, applied by the database engine per row.

### Reading with non-omission

For the read leg, the app asks dregg-query for an attested conjunctive query
over the receipt fact-base (`who holds which cap`, `which transfers exceeded X`,
…). The answer carries a `RangeCertificate` openable against the receipt-log
MMR root, so the consumer re-derives the answer locally and is certain no
qualifying row was dropped (`dregg-query/src/attested.rs`).

---

## 3. The trust story: ONE kernel decision across kernel + SQL

This is the load-bearing claim and the reason the store is more than a
convenience.

### One decision, two surfaces

The capability decision — does this token admit this action on this resource at
this time — is made in exactly one place: `dregg_auth::credential`'s verify,
whose semantics are the machine-checked ones in `metatheory/Dregg2/Authority/`.
pg-dregg's `authz::decide` (`pg-dregg/src/authz.rs`) delegates the decision
wholesale to that proven core; it adds only conventional integration (a
verified-credential LRU so the per-row cost collapses to a `Pred` re-eval, and an
instant-revocation registry). The kernel exercises the *same* `dregg_auth`
verify when an agent takes a turn. So:

> A row's RLS gate, the kernel's turn-authority check, and any out-of-database
> verification of the same token all reach the SAME verdict, because they call
> the SAME proven decision from the SAME token.

There is no second authority model to drift. The assurance boundary is named
honestly (`docs/design-frontiers/PG-DREGG-DX.md` §6, the honest-gaps burn-down):
the *decision* is verified; the *integration*
(the GUC plumbing, the LRU, the per-row invocation) is conventional extension
code, tested directly in the postgres-free core.

### Two teeth: RLS + non-omission

The store's guarantee has two independent teeth that compose:

1. **RLS (write/row leg) — a row you can't cap-reach is INVISIBLE.** The policy
   `USING (dregg_admits('read', encode(row_cap,'hex')))` runs the kernel
   decision per candidate row. A token from the wrong issuer, an expired token,
   a revoked token, or a token whose caveats do not admit the row's `row_cap` —
   all yield a denied decision, and the row is filtered out by the database
   engine. An attenuated token sees a strict subset (the no-amplify property).
   Proven in `pg-dregg/tests/cap_secured_store.rs`:
   - `rls_shows_only_cap_reachable_rows` — an org/42 token sees the three org/42
     rows, the org/99 rows are invisible;
   - `attenuated_token_sees_a_strict_subset` — narrowing to `org/42/public/`
     hides the private row, and the child's visible set ⊆ the parent's;
   - `wrong_or_overbroad_token_sees_nothing` — a foreign-issuer / garbage /
     expired token sees zero rows (fail-closed);
   - `instant_revocation_vanishes_rows_on_the_next_scan` — a revoked token's
     rows vanish on the very next scan, even with the verify cached hot;
   - `no_issuer_key_hides_the_whole_table` — no trust root ⇒ empty store, never
     wide-open.

2. **Non-omission (read leg) — a query can't silently OMIT rows.** RLS controls
   what you are *allowed* to see; the certificate proves that, of what you are
   allowed to see, *nothing was hidden*. A dregg-query answer carries a range
   opening against the receipt-log MMR root (`server_cannot_omit_position`,
   the Rust embodiment of `metatheory/Dregg2/Lightclient/MMR.lean`). The
   verifier re-derives the answer from exactly the certified receipt range and
   rejects a server that drops a qualifying row. The CALM grade rides along, so
   a finalized-dependent answer (`granted ∧ ¬revoked`) is honestly marked
   "fresh as of height H" rather than passed off as final. Proven in
   `dregg-query/tests/cap_secured_read.rs`:
   - `attested_read_returns_rows_with_a_verifying_certificate` — held caps + a
     verifying certificate;
   - `the_calm_grade_flags_the_finalized_dependence` — the negated query is
     graded finalized-dependent, fresh as of the revocation height; a positive
     query is monotone;
   - `a_server_that_omits_a_row_is_caught` — dropping a grant receipt while
     keeping the claimed range is rejected by the certificate;
   - `the_certificate_survives_the_wire` — the answer round-trips JSON and still
     verifies.

A hand-rolled SQL view gives you neither tooth: its predicate is a second
authority model (drift), and a `WHERE` clause that silently returns fewer rows
than it should is undetectable. The cap-secured store makes both classes of bug
structurally impossible.

---

## 4. builders-dev adoption: the smallest real slice for David

builders-dev is a Cloudflare-edge-native, multi-tenant SaaS (Workers + Durable
Objects + D1) where humans and agents are equal-tier peers, with authority tiers
1–4 on memberships, GitHub-OAuth→JWT sessions, MCP bearer keys, and team-scoped
queries with trust-header stripping at the edge (`docs/deos/BUILDR-INFRA-FIT.md`).
Its multi-tenancy today is query discipline; cross-team leakage is *un-queried*,
not *unreachable*.

The cap-secured store maps each hand-rolled mechanism onto one kernel decision:

| builders-dev today | cap-secured store | what changes |
|---|---|---|
| team-scoped queries + edge trust-header stripping | RLS `USING (dregg_admits('read', team_cap))` | cross-tenant leakage becomes *unreachable* (a cap you don't hold), not merely *un-queried* |
| authority tiers 1–4 on memberships | cap attenuations | a tier is a narrowing of a team cap; a downgrade is an attenuation, instant and non-amplifiable |
| hand-rolled RLS / scope predicates | one `dregg_admits` policy per table | the second authority model disappears — no predicate to drift |
| Analytics Engine / `budget_spend_events` audit rows | receipts | every state-change is a verifiable `TurnReceipt`, not a self-emitted analytics row |
| MCP bearer keys + scope-globs in D1 | attenuated tokens | the bearer IS the cap; its scope is its caveats, verified offline |

**The smallest adoptable slice (no rewrite).** builders-dev keeps its
Cloudflare front; it adds the bundle as the **multi-tenant system-of-record**
behind a Worker (a `postgres` reachable from Workers via Hyperdrive, or a
sidecar). The migration is mechanical and incremental:

1. Stand up the bundle (PG18 + pg-dregg) and set `dregg.issuer_pubkey` to the
   team's trust root. Mint team root caps out-of-database (the production
   posture; the private key never enters postgres).
2. Pick ONE leaky table (say, the team's documents / council artifacts). Add a
   `row_cap bytea` column = the team cell id, enable RLS, and add the single
   `dregg_admits('read', encode(row_cap,'hex'))` policy. Delete the hand-rolled
   `team_id = …` predicate.
3. The Worker, on a request, `SET dregg.token` to the session's attenuated team
   cap (login = receiving your root cap; a session = the cap-tree you hold;
   logout = revoking it — `docs/deos/SESSION-LOGIN.md`). Every query in that
   session is now cap-gated by the engine.
4. For audit, the table's writes flow as receipts; for "who holds what" reads,
   use dregg-query's attested conjunctive read so the answer cannot silently
   drop a row.

The value is not a capability builders-dev lacks — it is the
*cross-team-leakage class* and the *forged-OK / silent-omission class* of bug
made structurally impossible, behind one decision instead of many. That is the
kind of value that justifies a small adoption, not a rewrite.

---

## 5. Status and the honest seam

- **Runnable today (postgres-free core, proven by `cargo test`):** the RLS
  row-filter semantics (`pg-dregg/tests/cap_secured_store.rs`, 5 tests) and the
  attested read with non-omission certificate
  (`dregg-query/tests/cap_secured_read.rs`, 4 tests). These exercise the EXACT
  decision core the SQL policy and the read face run.
- **The pgrx path** (`cargo pgrx test pg18`) runs the same `authz::decide`
  behind the live SQL policy; it needs `cargo-pgrx` + a managed PostgreSQL 18
  and is not run by the postgres-free suite. The split is documented in
  `pg-dregg/Cargo.toml`.
- **The bundle packaging** (a one-command PG18 + auto-loaded extension +
  pre-set issuer key) is the next deos-distribution step
  (`docs/deos/DEOS-DISTRIBUTION.md`); the extension and read face it bundles are
  the pieces proven here.
- **Tier-C proof gate — the crate-split port is DONE** (`tier-c`/`tier-d`
  features). The circuit crate-split retired the `prover` feature and moved the
  IVC recursion tower to `dregg-circuit-prove`; pg-dregg's `tier-c` dep and
  `src/attest.rs` import now point at it (`pg-dregg/Cargo.toml` wires both the
  `tier-c` dep and the dev-dep to `../circuit-prove`; `attest.rs:436` calls
  `dregg_circuit_prove::ivc_turn_chain`). The `tier_c_real_proof.rs` integration
  test is fully ported — it is `#![cfg(feature = "tier-c")]` and imports
  `dregg_circuit_prove::{ivc_turn_chain, joint_turn_aggregation}`. What remains
  is a deliberate build-cost gate, not an unfinished port: the Tier-C *chain*
  re-validation ships unconditionally; only the heavyweight *proof* attestation
  sits behind the `tier-c` feature (off by default so the postgres-free core and
  the cap-secured-store slice stay circuit-free).
```
