# pg-dregg — the developer experience frontier

*Your node IS your postgres. Reads are free SQL; state mutates only through
verified turns. The lowest-friction door into dregg is a `psql` prompt.*

This document is a north star for the pg-dregg developer experience — not a rigid
spec. It teaches what pg-dregg **is** today, names the **buildable next slices**,
sketches the **killer demo**, walks the **developer journey** from both sides, and
keeps an **honest gap ledger**. The substrate it builds on is live: Tiers A, B,
and C run on PostgreSQL 18 right now (the `pg-dregg` crate + `node/src/pg_mirror.rs`).

---

## 0. The one-paragraph vision

A dregg node persists its verified state, and that state is **ordinary
PostgreSQL** — queryable with `SELECT`, gated by the same capability tokens that
authorize a tool call, written only by verified turns. A postgres-heavy developer
who has never heard of dregg installs one extension and trades their hand-rolled
RLS-over-JWT for **attenuable, offline-verifiable, instantly-revocable object
capabilities** — gaining provable non-amplification (a delegate can only ever see
a subset of its grantor) with zero new infrastructure. A dregg developer who needs
a query surface, an explorer, or a write path reaches for `psql` as naturally as
for the SDK: the cell graph, the delegation tree, the receipt chain, and the
universal-memory multiset are all just tables and views. The endgame (Tier D) is a
guarantee no separate node can offer: **one database transaction that mutates dregg
kernel state and your application's own tables atomically** — they commit together
or not at all.

---

## 1. The angle, stated sharply

dregg's hardest adoption problem is that integrating it has always meant *running
dregg* — a node, a blocklace, an FFI seed, an SDK, a mental model of cells and
turns. pg-dregg inverts the on-ramp. The lowest-friction "hello, dregg" is not
`cargo run`; it is:

```sql
CREATE EXTENSION pg_dregg;
SELECT set_config('dregg.token', 'dga1_…', true);
SELECT * FROM documents;   -- the rows your capability admits, and only those
```

Postgres is the most widely deployed stateful substrate on earth. Meeting
developers there — **"bring your capabilities to where your data already lives"** —
is a wider front than any SDK. And it cuts both ways:

- **the postgres developer** gains verified object-capability authorization
  (delegation, attenuation, time-boxing, instant revocation, explainable denial)
  as a drop-in RLS policy substrate — *without standing up any dregg node at all*.
  The authorization core is postgres-bound but node-free: a `dga1_…` token verifies
  offline against a published issuer public key.
- **the dregg developer** gains a queryable, cap-gated view of their node's state —
  `SELECT`s replace bespoke query endpoints, the explorer *is* the rows you may
  read, and the same bearer token gates both the kernel and the SQL.

The two perspectives converge on **one decision** (`dregg_admits`) and **one trust
root** (the issuer public key). That convergence is the product.

---

## 2. What pg-dregg is today (teach-what-is)

pg-dregg is a `cargo-pgrx` extension (`pg-dregg/`) plus a node-side mirror writer
(`node/src/pg_mirror.rs`). It is organized as four tiers; A/B/C are live on pg18,
D is the frontier.

### The spine invariant

> **Reads are free SQL; state mutates ONLY through verified turns.**

Every row in the `dregg.*` schema is the post-image of a turn the kernel already
verified. Applications `SELECT` freely; a bare `INSERT/UPDATE/DELETE` by an
application role is forbidden at the privilege layer. The only writer is
`dregg_kernel` (a `BYPASSRLS`, `SECURITY DEFINER` role), and even its writes pass
the chain gate in Tier C. The schema is **emitted from the same Rust that defines
the row types** (`mirror::ddl::tier_b`), so the tables cannot drift from the code —
pinned by the `emitted_ddl_agrees_with_committed_sql_file` test.

### Tier A — capabilities as Row-Level Security *(live, proven)*

The authorization core (`pg-dregg/src/authz.rs`, postgres-free, `cargo test`-proven)
decodes and verifies a `dga1_…` credential against the issuer public key (delegating
to the proven `dregg-auth::credential`), then evaluates the caveat predicate over
`(action, resource, now)`. The thin `#[pg_extern]` wrappers (`src/lib.rs`, behind
the `pgrx` feature) expose it:

| function | meaning |
|---|---|
| `dregg_admits(action, resource)` | the ergonomic face — reads the `dregg.token` session GUC + `now()`; for `USING (dregg_admits('read', id::text))` |
| `dregg_cap_admits(token, action, resource, now)` | the explicit decision (STABLE, parallel-safe, STRICT, fail-closed) |
| `dregg_cap_explain(...)` | the human-readable reason — `"allowed"` or the first violated caveat (debugging the vanished row) |
| `dregg_cap_subject(token)` | the confined identity the token names (for actor-column joins / audit) |
| `dregg_attenuate(token, caveats)` | narrow a token (IMMUTABLE; no issuer key; the holder's right; `attenuate_subset` proves the result is a strict subset) |
| `dregg_revoke(token)` / `dregg_cap_not_revoked(token)` | instant per-credential revocation |

Two design decisions are load-bearing and correct: `dregg_cap_admits` is **STABLE,
not IMMUTABLE** (revocation can flip a verdict within a statement, so the planner
must not fold it across rows), and the issuer key is a **`Sighup` GUC, never a
session `SET`** (a session cannot point verification at a key it controls and forge
admits). A malformed/absent key denies everything. Nothing is open by default.

The thesis — *a delegate sees a strict subset of its grantor* — is proven through
the SQL boundary: `rls_gated_table_narrows_row_visibility` (root token sees 3 rows,
an attenuated token sees 2) and `instant_revocation_makes_rows_vanish` (revoke,
and the same `SELECT` returns zero of that credential's rows on the next statement).

### Tier B — dregg state as queryable tables *(live on pg18)*

The node's verified state is mirrored into postgres. The honest model is **one Blum
multiset** — `dregg.memory` over `Domain × κ`, where `Domain ∈ {registers, heap,
caps, nullifiers, index}` (`docs/UNIVERSAL-MEMORY.md`). A new state component is a
new domain *value*, never a new table. The typed tables (`dregg.cells`,
`dregg.turns`, `dregg.capabilities`) and views (`cell_balances`, `cap_edges`,
`receipt_chain`, `cap_attenuations`, `cell_fields`, `turn_effects`,
`canonical_cells`) are **derived boundary projections** over that multiset.

The live writer is `node/src/pg_mirror.rs::pg_live::PgSink` (behind the
`pg-mirror-live` feature, opt-in via `DREGG_PG_MIRROR_URL`). It tails the durable
commit log and, per verified turn, projects a `MirrorBatch` (the one piece that
needs `dregg-cell`: decoding a live `Cell` into rows) and ships it over
`tokio-postgres` in a single transaction — the turn row, each touched cell via the
pg18 `dregg.merge_cell` MERGE upsert, each capability edge, each memory cell. The
batch commits with its post-images or not at all, so a reader never sees a torn
mirror. `ON CONFLICT DO NOTHING` makes a re-shipped ordinal idempotent (crash-safe
replay).

The pg18 leverage is exploited, not decorative: **MERGE + RETURNING old/new**
(`dregg.merge_cell` returns `'INSERT +1000000'` / `'UPDATE -500'` — the action and
balance delta in one atomic statement), **VIRTUAL generated columns**
(`cell_root_hex`, `balance_field` computed on read, no stored bytes), **`JSON_TABLE`**
(`cap_attenuations` explodes a cap's `allowed_effects` array into one row per
effect — the no-amplification audit surface), **builtin-C collation**
(`canonical_cells` gives deterministic, version-stable byte ordering).

### Tier C — the verified-store gate *(live)*

`dregg_install_tier_c()` installs `dregg.commit_log` (the only door to state) and a
`BEFORE INSERT` trigger that runs `dregg_verify_turn` — the **real anti-substitution
tooth**: turn *N*'s post-state root must be turn *N+1*'s pre-state root, and the
ordinal must be the next expected one, read from the live `dregg.turns` head. A
tampered, reordered, or forged batch is **refused by the database engine** without
re-running the verifier. This is the exact same `mirror::verify_chain_step` the
node-side `RootChain::extend` runs, so a correct node never produces a batch the pg
side rejects, and a tampered one breaks the chain on both sides
(`pg_side_refuses_a_tampered_batch`).

What Tier C is **not** (named honestly, §10.2 of the crate docs): it is not a
per-turn STARK re-proof. A `CommitRecord` carries no per-turn proof — proof
soundness over a *range* is the whole-chain IVC light client's job
(`circuit::ivc_turn_chain::verify_turn_chain_recursive`, the heavyweight `tier-c`
cargo feature). The realizable per-row gate is the structural chain check, and it
fails closed; it is never stubbed to `TRUE`.

### Tier C-write — submit a verified turn FROM postgres *(live)*

`dregg_install_write_outbox()` installs `dregg.submit_queue` and a `submit_gate` RLS
policy. `dregg_submit_turn(signed_turn bytea, agent bytea)` enqueues a signed turn,
**gated by `dregg_admits('submit', encode(agent,'hex'))`** — a role submits exactly
the turns its capability authorizes; an unauthorized agent's enqueue is refused by
Row-Level Security. Crucially, the function is **not** `SECURITY DEFINER`, so the
`WITH CHECK` policy bites against the calling role. **Postgres never executes** — the
turn is queued for the node, which drains it through the real verified executor; only
verified post-state lands. Reads stay free SQL; writes stay verified-only.

pg18's front-door features are wired here too: a `login` **event trigger**
(`dregg_install_login_binding` + `dregg_bind_role`) binds a connecting pg role to its
dregg agent identity at connection time (so a plain `SELECT` is already cap-narrowed,
no app-side token presentation), and the **uuidv7** queue key doubles as an audit
signal — `submit_queue_audit` recovers the enqueue time and version *from the key
itself*. This is the seam where pg18 OAuth (a `pg_hba.conf` deployment concern) meets
dregg: OAuth authenticates an external identity to a pg role; `dregg_bind_role` binds
that role to a dregg capability.

### Tier D — the executor as a pg function *(the north star)*

The frontier: `dregg_submit_turn_inproc(envelope)` executes a verified turn **inside
the postgres backend**, in the same transaction that also `UPDATE`s your application's
own tables. Kernel state and app state commit together or not at all. **No separate
node can offer that cross-domain atomicity** — it is the structural payoff of "your
node IS your postgres." Gated on the pg/Lean process-model spike (§5).

---

## 3. The killer demo

**"Atomic cap-gated checkout: one transaction moves the money AND ships the order —
or neither — and a delegate provably cannot overreach."**

The demo is a tiny commerce app: an `orders` table (the developer's own data) and a
`dregg.cells` balance ledger (kernel state). It runs entirely in `psql`, and it
lands four punches that, *together*, no other system delivers in one place:

1. **Reads are your capabilities.** A buyer presents their token; `SELECT * FROM
   orders` and `SELECT * FROM dregg.cell_balances` return only the rows that token
   admits. Attenuate the token to a single merchant prefix — the other merchants'
   rows **vanish**, a strict subset, no policy or data changed. (`USING
   (dregg_admits('read', …))` + `dregg_attenuate`.)

2. **Delegation provably cannot amplify.** The buyer hands a shipping agent a
   *narrowed* token — `read` on their orders only, no `pay`. The agent's `SELECT`
   sees the orders; the agent's attempt to submit a payment turn is **refused by
   RLS** at enqueue (`submit_gate` over `dregg_admits('pay', …)`). The
   `cap_attenuations` view shows, as queryable rows, exactly which effects the
   delegate may exercise — and that it is a subset of the grantor's.

3. **The atomic cross-domain commit (Tier D).** The checkout is ONE transaction:

   ```sql
   BEGIN;
     UPDATE orders SET status = 'paid' WHERE id = :order;          -- app data
     SELECT dregg_submit_turn_inproc(:signed_pay_turn);            -- kernel state
   COMMIT;   -- the order ships and the balance moves, or NEITHER does
   ```

   Kill the connection between the two statements and **nothing** changed: no half-
   paid order, no orphaned balance move. This is the line a developer cannot draw
   with any node-beside-database architecture.

4. **The receipt chain is a light client, in SQL.** `SELECT ordinal, prev_root,
   ledger_root FROM dregg.receipt_chain` walks the hash chain; each `prev_root`
   equals the prior `ledger_root`. Tamper with one row's post-image and the chain
   visibly breaks (`dregg_verify_turn` refuses it). The auditor needs no node — just
   `psql` and the published issuer key.

**Why it lands:** every piece is real today *except* punch #3's `_inproc` variant
(buildable next, §4). Punches #1, #2, and #4 run on the live Tier A/B/C substrate
right now via `scripts/e2e-live.sh`. The demo *is* the evaluation artifact for the
pug handoff: a stranger clones, runs one script, and watches capabilities narrow
rows, refuse an overreach, atomically commit across domains, and expose a walkable
proof chain — all in the prompt they already know.

A staged fallback keeps the demo honest before Tier D lands: punch #3 runs as the
**outbox** form (`dregg_submit_turn` enqueues inside the `BEGIN`; the node drains it
and the mirror reflects the result), which demonstrates the RLS submission gate and
the verified-only write discipline. The atomicity claim is then scoped precisely:
"the *submission* is transactional with the app write; the *execution* settles
asynchronously" — the Tier-D `_inproc` upgrade is what collapses that gap to true
cross-domain atomicity.

---

## 4. The buildable shape (concrete next slices)

Ordered by leverage. Each is wide-safe (the pg-dregg crate is a standalone
workspace, so it does not touch the metatheory build or the VK rotation) or
node-side-additive (behind the opt-in `DREGG_PG_MIRROR_URL` / `pg-mirror-live`
flags, so the default node is unchanged). None is blocked on the rotation cutover.

### S1 — The node-side queue drainer (close the C-write loop) *(highest leverage)*

`dregg_submit_turn` enqueues into `dregg.submit_queue` today, but the shipped path
has no drainer — the status never walks `pending → executed | refused`. Build the
node-side loop: tail `submit_queue` (the symmetric read-side of `pg_mirror.rs`'s
write side), feed each signed turn to the **real verified executor**, and write back
`status` + `receipt_hash` / `error`. This is the missing half of the bidirectional
story and the precondition for the demo's punch #3 in its outbox form. It reuses the
exact trust position the mirror already holds (the node is the only writer; the
executor is the only thing that decides). Lands as a new node service module
(sibling to `channels_service.rs` / `storage_service.rs`), driven by `LISTEN/NOTIFY`
on enqueue so it is not a poll loop.

### S2 — Tier D spike: `dregg_submit_turn_inproc` *(the north-star slice)*

The process-model question: can the verified Lean executor (already FFI-exported and
node-invoked) be linked into a postgres backend and called from a `#[pg_extern]`,
inside the SQL transaction? The spike answers three things — (a) the executor's
side-effect surface is the in-process kernel-state map, which is exactly what the
mirror already projects, so executing-then-mirroring in one backend transaction is
coherent; (b) the FFI's memory/allocation model is compatible with a postgres
backend's palloc-context lifecycle (the known risk); (c) the proving step stays OFF
the transaction path (proofs attach asynchronously at the trust boundary, per the
proving-modality dial — a `BEGIN; … COMMIT;` must not block on a STARK). Deliverable:
one transaction that `UPDATE`s an app table and mutates a `dregg.cells` balance,
proven atomic by a kill-between-statements test. The `tier-d` cargo feature already
declares the path (`tier-d = ["tier-c"]`).

### S3 — In-SQL minting for dev/single-tenant *(on-ramp friction killer)* — **LANDED**

Today's out-of-band minting (`examples/mint.rs`; `dregg_mint`, a dev-only
`SECURITY DEFINER` extern reading the superuser-only `dregg.issuer_privkey` GUC)
imposes a first-ten-minutes friction: "go run a Rust binary to get a token." The
**dev-mode mint ergonomics** remove it: `dregg_dev_mint(subject, actions text[],
resource_prefix text, ttl interval)` composes the common caveat shape (action-`AnyOf`
or a single `AttrEq` + resource-prefix + the shared `NotAfter`) so a newcomer never
hand-writes `Pred` JSON, and a loud `dregg_issuer_status()` reports whether a verify
key is configured (and its id), whether dev minting is enabled, and — when the verify
key is absent — the named `EVERYTHING DENIES` fail-closed mode, so it is *discoverable*,
not silent. The production recommendation (mint out-of-database, never place the
private key in postgres) **stays the default**: `dregg_dev_mint` routes through the
*same* `authz::dev_mint → authz::mint_token` path as `dregg_mint`, so with no
`dregg.issuer_privkey` it RAISES (never a silently-minted token) — it does NOT bypass
the issuer-key discipline.

**Built:** `pg-dregg/src/authz.rs` (the postgres-free core: `dev_mint`,
`dev_mint_caveats_json`, `issuer_status` / `issuer_status_text`, `cargo test`-proven)
+ the `dregg_dev_mint` (`SECURITY DEFINER`, `ttl` resolved by postgres's own clock)
and `dregg_issuer_status` (`STABLE`) `#[pg_extern]`s in `src/lib.rs`. Tested through
real SQL against the live pg18 (`dev_mint_produces_a_token_the_admit_path_accepts`,
`dev_mint_token_narrows_rows_through_rls`,
`dev_mint_without_a_key_raises_not_silently_mints`,
`issuer_status_reports_the_configured_keys`; `cargo pgrx test pg18` = 88/88 green),
and exercised interactively on the running pg18:28818 (the no-key path errors loudly;
the verify-key-only status names the key id + "dev minting DISABLED — Production
posture"; the enabled path mints a `dga1_…` token `dregg_cap_admits`/`dregg_cap_explain`
accept and that narrows an RLS-gated table 3→2 under attenuation). The on-ramp doc is
`docs/QUICKSTART-dregg-dev.md` §7b; the "all my rows vanished?" diagnostic is wired
into `docs/QUICKSTART-pg-user.md`.

### S4 — The cap-gated query cookbook (the explorer-as-capabilities surface) *(LANDED)*

The dregg-developer journey's payoff is "the explorer is your capabilities." A
small library of **parameterized, RLS-gated views and recursive queries** as
copy-paste recipes: the delegation tree (`WITH RECURSIVE` over `cap_edges` rooted at
one cell), the conservation check (`SELECT sum(balance) FROM dregg.cells` = genesis
total), per-cell time-travel (`cell_history` by `(id, ordinal)`), the receipt-chain
walk with an in-SQL non-omission assertion (`prev_root = lag(ledger_root)`), and the
no-amplification audit (`cap_attenuations` joined against the grantor's effects). Each
is a teaching artifact AND a real tool. This is pure SQL + docs — zero build risk,
immediate handoff value.

**Built:** `pg-dregg/sql/cookbook.sql` (the seven runnable recipes, parameterized via
psql `\set`), `pg-dregg/sql/cookbook-seed.sql` (a demo delegation graph + per-cell
history with one deliberate amplification for the audit to catch), and
`pg-dregg/docs/COOKBOOK.md` (the teaching walk-through with live output). Recipes 1–6
are tested against the live pg18 mirror (`pg_dregg_mirror`) and run top-to-bottom with
zero errors; recipe 6's narrowing is observed with real minted `dga1_…` tokens (1 / 6 /
0 rows for prefix-`5e` / `""` / no-token); recipe 7's write gate is the Tier-C engine
refusing a non-chaining turn on `pg_dregg_e2e`. The **browser twin** is
`site/explorer/caps-as-rows.html` — present a capability, watch the cell rows narrow,
the RLS gate respected (a filtered row's value is redacted, never shown) and explained
(`dregg_cap_explain`'s reason, per row). One glass in SQL, one in the browser, both
rendering the identical seeded world.

### S5 — Predicate-algebra reach (the lamesauce exit, applied to pg)

The caveat predicate algebra is currently `AttrEq / AttrPrefix / NotAfter / AnyOf /
AllOf / Not` — expressive for namespaces and time, but a row predicate like `balance
>= 500` is **not** in it (named honestly in the crate's own
`pred_jsonpath_filters_the_mirror_as_a_read` test). As the metatheory predicate
uplift lands richer atoms (the §8 guard-algebra ladder — affine bounds, membership,
heap atoms), surface them through `dregg_pred_jsonpath` so the *same* algebra that
gates a kernel write becomes a queryable jsonpath over the mirror. The discipline is
already proven sound: `pred_jsonpath_matches_agree_with_real_authz` asserts the
jsonpath verdict equals the chain-verified `dregg_cap_admits` verdict on every row.
Extending the algebra extends both the gate and the read in lockstep — one predicate
language, two faces.

### S6 — Fresh-clone build story (the standalone-workspace seam)

pg-dregg is deliberately a standalone workspace (out of the parent `members` list) so
its `cargo-pgrx` cdylib build does not pull postgres bindings into the shared
`./target` during concurrent lanes / the VK rotation. That is correct, but it is a
**seam in the handoff bar** (stranger-usable, fresh-clone, no tribal knowledge). Build
the on-ramp closure: a single `pg-dregg/scripts/setup.sh` that checks for
`cargo-pgrx` + a managed pg18, prints the exact `brew`/`cargo install`/`cargo pgrx
init` commands if absent, installs the extension, sets the dev issuer key, and runs
`e2e-live.sh` — so "clone, run one script, see it work" holds without ember in the
loop. Pair with an evaluator's README (what it IS / the guarantees / the honest
assurance boundary / the first ten minutes).

---

## 5. The developer journey (both perspectives)

### The postgres developer — "I never want to run a dregg node"

1. **Minute 0** — `cargo pgrx install`; `CREATE EXTENSION pg_dregg;`. Set
   `dregg.issuer_pubkey` in `postgresql.conf` (the published trust root).
2. **Minute 2** — take any table, `ENABLE ROW LEVEL SECURITY`, and write `CREATE
   POLICY cap_read ON documents FOR SELECT USING (dregg_admits('read', id::text))`.
   It is the `CREATE POLICY` they already know — the only new thing is the function.
3. **Minute 4** — present a token (`SELECT set_config('dregg.token', 'dga1_…',
   true)`), watch the rows narrow. Present an attenuated token, watch the private
   rows vanish — the no-amplification property, observed, not asserted.
4. **Minute 6** — `dregg_revoke(...)`; the same query returns zero rows on the next
   statement. `dregg_cap_explain(...)` names *why* a row was filtered (the
   miserable-to-debug vanished-row problem, solved).
5. **The win**, as a table:

   | wanted | hand-rolled RLS over JWT | pg-dregg |
   |---|---|---|
   | delegation (hand a sub-agent less, offline) | role DDL, central | attenuate a token, no round-trip |
   | provable narrowing (child ⊆ grantor) | inexpressible | the no-amplify property, enforced |
   | time-boxing | thread an `expires_at` column | `NotAfter` caveat on the token |
   | per-credential revocation | `DROP POLICY`, coarse | `dregg_revoke`, instant, per-token |
   | explainable denial | the row just vanishes | `dregg_cap_explain` names the reason |

They added one extension, one GUC, and policies in a closed, proved capability
calculus — and **never ran a node**.

### The dregg developer — "I want my node's state as SQL"

1. **Minute 0** — start the node with `DREGG_PG_MIRROR_URL=postgres://…` and the
   `pg-mirror-live` feature. Every verified turn now flows into `dregg.*` (gated by
   the `RootChain` tooth). The on/off switch is that one env var.
2. **Minute 2** — `SELECT cell, balance, nonce FROM dregg.cell_balances ORDER BY
   balance DESC`. The ledger, as a query. `SELECT sum(balance) FROM dregg.cells` —
   conservation, checked.
3. **Minute 4** — the delegation graph: `WITH RECURSIVE` over `dregg.cap_edges` walks
   the reachability tree from one cell. The light client: `dregg.receipt_chain` is the
   walkable hash chain.
4. **Minute 6** — `SELECT set_config('dregg.token', 'dga1_…', true)` and the same
   views narrow to *your* admitted cells. The explorer is your capabilities; your SDKs
   query through pg with the bearer token they already hold — no separate
   authorization surface.
5. **Minute 8** — submit FROM postgres: `dregg_install_write_outbox()`, present a
   `submit`-scoped token, `dregg_submit_turn(:turn, :agent)`. RLS refuses a turn for
   an agent your token does not authorize. The node drains the queue through the real
   executor; only verified post-state lands.

Both journeys end at the same place: **one decision, one trust root, one bearer
token** — gating both the kernel and the SQL.

---

## 6. Honest gaps (the burn-down, not a ledger)

These are real, named, and each carries the slice that closes it. A labeled seam is a
problem to drive to closure, not a wall.

- **The queue drainer is unbuilt.** `dregg_submit_turn` enqueues but nothing drains
  the shipped path — `status` never advances past `pending`. The bidirectional write
  story is half-present. → **S1.** (This is the single most load-bearing gap: until it
  lands, the write path is an RLS-gated inbox with no consumer.)
- **Tier D is a spike, not a slice yet.** Cross-domain atomicity — the structural
  payoff — depends on linking the Lean executor into a postgres backend (the
  palloc-context / FFI-lifetime risk is unproven, and proving must stay off the txn
  path). The `tier-d` feature declares the path; the spike (S2) decides feasibility.
  The killer demo's punch #3 runs in its outbox form until then.
- **The per-row gate is structural, not a proof.** Tier C re-validates the *chain*
  (anti-substitution), which is the realizable per-row tooth; it is **not** a per-turn
  STARK re-proof. Proof attestation is range-level IVC (`circuit::ivc_turn_chain`,
  the heavyweight `tier-c` cargo feature), not wired to per-row. A `CommitRecord`
  carries no per-turn proof — this is a deliberate, documented boundary, not a bug,
  but a consumer who wants "this row is proof-attested" must walk the IVC range, not
  read a column.
- **Minting the issuer secret out-of-band — the on-ramp's first friction — is
  CLOSED for dev/single-tenant (S3, landed).** `dregg_dev_mint` composes the common
  capability shape in SQL (no hand-written `Pred` JSON) and `dregg_issuer_status`
  makes the "no key ⇒ everything denies" mode discoverable. The discipline is intact:
  `dregg_dev_mint` shares `mint_token`'s path, so no `dregg.issuer_privkey` ⇒ a loud
  RAISE, never a silent token; the **production** path still mints outside postgres
  entirely (the private key never enters the database) and remains the default.
- **The predicate algebra is namespace+time, not arithmetic.** `balance >= 500` is not
  expressible as a caveat today (only attribute/prefix/temporal/boolean). This is the
  "lamesauce" critique at the pg surface. → **S5**, in lockstep with the metatheory
  uplift, with the jsonpath-agrees-with-authz test as the guardrail.
- **The assurance boundary is named, not erased.** The capability *decision* is the
  verified `dregg-auth` decision (the Lean↔Rust differential anchors it). The
  *integration* — the GUC plumbing, the verified-credential LRU, the revocation
  registry, the per-row invocation — is conventional extension code, tested directly
  in `core` but **not formally verified**. pg-dregg claims exactly the dregg
  decision's soundness through the SQL boundary, and no more. This is the honest scope
  for the evaluator's README.
- **Revocation is backend-local.** The instant-revocation registry that
  `dregg_cap_not_revoked` consults lives per-backend; a clustered deployment needs a
  shared `dregg.revoked` table the policy also joins (the design notes this; the
  default bounded-staleness path is the short-`NotAfter` TTL). Named, with the cluster
  shape sketched, not yet built.
- **The standalone-workspace seam.** Correct for build isolation (protects the shared
  `./target` from pgrx's postgres-binding build), but it means the fresh-clone story
  needs its own setup path to meet the stranger-usable bar. → **S6.**

---

## 7. Why this is the right frontier

dregg's thesis has always been *the verified accountability substrate that other
loops integrate against, not the loop itself*. pg-dregg is that thesis made
maximally low-friction: the integration seam is a `CREATE POLICY` and a bearer token,
the substrate is the database the developer already runs, and the guarantee that
justifies the whole edifice — provable non-amplification, instant revocation,
verified-only writes, and (at Tier D) cross-domain atomicity — arrives without asking
anyone to adopt a node first. The postgres user gets verified capabilities for free;
the dregg developer gets a queryable cap-gated node; and both meet at one decision
over one trust root. The on-ramp *is* the product.

---

## Appendix — the load-bearing files

- `pg-dregg/src/lib.rs` — the `#[pg_extern]` surface + the `#[pg_test]`s (the M1
  thesis through real SQL).
- `pg-dregg/src/authz.rs` — the postgres-free authorization core (decode/verify/LRU/
  revocation/attenuation), `cargo test`-proven.
- `pg-dregg/src/mirror.rs` — the row projections, the `Domain × κ` universal-memory
  model, the DDL emitter (`tier_b` / `tier_c` / `write_outbox` / `login_binding`), the
  `RootChain` anti-substitution tooth.
- `node/src/pg_mirror.rs` — the live node→pg writer (`pg_live::PgSink`), the
  `MirrorBatch` projection, the chain gate before shipping. The opt-in switch is
  `DREGG_PG_MIRROR_URL`.
- `pg-dregg/scripts/e2e-live.sh` + `sql/e2e-live.sql` — the standalone `psql`
  walk-through: rows land, the chain verifies, a tampered batch is refused, the
  write-path gate narrows submission. The demo skeleton.
- `pg-dregg/examples/mint.rs` — the out-of-band minting path (the issuer-secret
  on-ramp friction S3 addresses).
- `pg-dregg/docs/QUICKSTART-pg-user.md` / `QUICKSTART-dregg-dev.md` — the two
  perspectives' existing on-ramps.
- `pg-dregg/sql/cookbook.sql` + `sql/cookbook-seed.sql` + `docs/COOKBOOK.md` — the
  cap-gated query cookbook (S4): seven runnable, RLS-gated recipes (delegation tree,
  no-amplification audit, conservation, receipt-chain non-omission, time-travel,
  caps-as-rows, the write gate), tested against the live pg18 mirror.
- `site/explorer/caps-as-rows.html` + `caps-as-rows.js` — the browser twin: present a
  capability, watch the cell rows narrow (the RLS gate respected + explained). Linked
  from the explorer header ("Caps as rows").
