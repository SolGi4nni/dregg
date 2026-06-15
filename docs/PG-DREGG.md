# PG-DREGG — dregg verified object-capability authorization as a PostgreSQL-native RLS/policy layer

`pg-dregg` is a PostgreSQL extension (built with `pgrx`) that exposes dregg's
verified object-capability tokens as SQL functions, so an ordinary
postgres-heavy application gates row and table access with dregg capabilities —
attenuation, delegation, time-boxing, caveats, third-party discharge, offline
verification, revocation — in place of hand-rolled SQL Row-Level-Security
predicates. The application keeps its own schema and its own tables; what
changes is the *policy* a row is checked against: instead of
`USING (tenant_id = current_setting('app.tenant'))`, a policy reads
`USING (dregg_cap_admits(current_setting('dregg.token'), 'read', id::text, …))`,
and the decision is the same one dregg's kernel makes, from the same token.

This document is the proposal and study that precedes a `pgrx` prototype. It is
written from first principles in present tense; it does not narrate a
trajectory. The reference implementation it builds on is the `dregg-auth` crate
(`dregg-auth/src/credential/`), whose semantics are the machine-checked ones in
`metatheory/Dregg2/Authority/`.

---

## 1. The thesis

Modern applications are postgres-heavy. Their authorization lives in one of two
places, both unsatisfying:

- **Application-tier checks** — a service layer that decides, in imperative
  code, whether a request may touch a row, then issues an unconstrained query.
  The database trusts the application completely; a bug or an SQL-injection in
  the app tier is a total authorization bypass.
- **SQL Row-Level Security** — `CREATE POLICY … USING (predicate)`, where the
  predicate is hand-written SQL over session variables (the Supabase /
  PostgREST pattern: a JWT is swapped into `request.jwt.claims`, and policies
  read `current_setting('request.jwt.claims')::json->>'role'`). The database
  enforces, which is the right place, but the *policy language* is raw SQL
  boolean expressions over GUCs. That language structurally cannot express the
  capability discipline the application actually wants.

dregg already has a verified object-capability token whose authorization
semantics are proved in Lean and embodied, offline and dependency-light, in
`dregg-auth`. The thesis is to make **that token the policy substrate of
PostgreSQL RLS**: one capability token, presented once per session, authorizes
*both* against the dregg kernel (when the app also talks to dregg) *and*
against the application's plain postgres tables. The same `dga1_…` string a
sub-agent carries to call a dregg tool is the string a postgres policy checks a
`SELECT` against.

### Two first-class perspectives, one substrate

`pg-dregg` is designed to be first-class from **both** directions, and the same
extension serves both:

- **The postgres user's perspective.** Someone who lives in postgres: their
  existing tables gain dregg's verified caps (RLS) + provenance, with zero dregg
  infrastructure to learn beyond a token string. `CREATE EXTENSION`, set the
  issuer key, write `CREATE POLICY … USING (dregg_admits(…))`, present an
  attenuated token, watch the rows narrow. The capability discipline — provable
  attenuation, offline delegation, per-credential revocation, explainable denial
  — arrives without any of it leaking into their mental model beyond the policy
  line. The 10-minute path is `pg-dregg/docs/QUICKSTART-pg-user.md`.

- **The dregg developer's perspective.** Someone building on dregg: **postgres
  is a native dregg surface.** "Your node IS your postgres" — state is queryable
  SQL (`SELECT * FROM dregg.cells`), authorization is caps, the mirror is the
  store. They reach for pg as naturally as for the SDK: the commit log projects
  into queryable tables (cells / receipts / caps / the blocklace), the explorer
  is "your capabilities, expressed as the rows you may `SELECT`", and SDKs query
  through pg with the bearer token they already hold. The path is
  `pg-dregg/docs/QUICKSTART-dregg-dev.md`.

The first perspective is **Tier A** (caps as RLS, the M1 functions); the second
is **Tiers B/C/D** (state as tables → writes through the verifier → the executor
as a pg function). Circuit-free + offline is a property of **Tier A only**, not
a ceiling: `pg-dregg` authorizes the executor/circuit for the tiers that need
them (§8.1). Part II below is the second perspective in full.

### What hand-rolled SQL RLS structurally cannot express

A SQL `USING` predicate is a boolean expression over the current row and
session GUCs. It is **stateless, first-party, and non-delegable** by
construction. The capability properties below are not "hard to write" in SQL
RLS — they are *inexpressible*, because there is no token, no issuer signature,
and no attenuation chain for the predicate to reason over:

| Capability property | dregg-auth mechanism | Why SQL RLS cannot express it |
|---|---|---|
| **Attenuation chains** (a delegate holds strictly less than its grantor, provably) | `Credential::attenuate` appends a signed block; `attenuate_subset` proves the admitted-request set can only shrink | A GUC is a flat string; there is no notion of "this session's authority is a *narrowing* of another's", and nothing prevents a policy from reading wider claims than were granted |
| **Delegation** (hand a sub-agent a token offline, no issuer round-trip) | the biscuit / ed25519 block chain (`BiscuitGraph`); the holder of the tail key attenuates and re-signs | RLS has roles and `GRANT`, but role membership is centrally administered DDL — there is no bearer credential a principal can sub-delegate without a privileged operation |
| **Time-boxing** | `Pred::NotBefore` / `NotAfter` / `Within` (proved upward/downward-closed) | expressible only by hand-threading an `expires_at` column or comparing `now()` to a JWT `exp` claim the policy must re-parse every row |
| **Caveats** (arbitrary first-party predicates: resource prefix, attribute equality, n-ary boolean with negation at every level) | `Pred` algebra (`AttrEq` / `AttrPrefix` / `AllOf` / `AnyOf` / `Not`), fail-closed | each caveat must be re-encoded as bespoke SQL and re-audited; there is no closed, proved algebra and no guarantee the SQL faithfully reflects the granted constraint |
| **Third-party discharge** ("allow iff the compliance gateway has approved", offline) | `Caveat::ThirdParty` + macaroon-style bound `Discharge` (`MacaroonDischarge`); the gateway signs an approval bound to *this exact credential's tail* | RLS would need a synchronous join against an approvals table the gateway writes; there is no offline, replay-proof, cross-service approval token |
| **Offline verifiability** | `Credential::verify` needs only the issuer **public key** + the request facts; no network, no issuer, no node | a JWT can be verified offline, but a *capability* (with attenuation + caveats) cannot be reconstructed from JWT claims; the verification is not capability-shaped |
| **Revocation** | provider-side `RevocationRegistry` (Merkle non-membership proofs) + short token TTLs as the offline horizon | RLS revocation is `REVOKE`/`DROP POLICY` DDL, coarse and central; there is no per-credential revocation a verifier checks against a published root |
| **Explainable denial** | every `Refusal` / `Decision` names the violated requirement (`reason()`) | a row that fails `USING` simply disappears; the database gives no reason, which makes capability debugging miserable |

The structural point: SQL RLS is a *predicate evaluator*; dregg is a *capability
calculus with a signed, attenuable, offline-verifiable token*. `pg-dregg` lets
the predicate evaluator delegate its decision to the capability calculus.

---

## 2. The design — the SQL surface

`pg-dregg` is a `cdylib` postgres extension. It registers a small set of
immutable, parallel-safe SQL functions backed by `dregg-auth`. The headline
function is `dregg_cap_admits`.

### 2.1 The functions

```sql
-- The core decision. Returns TRUE iff `token` (a dga1_… credential string)
-- admits `action` on `resource` at clock `now`, verified OFFLINE against the
-- issuer public key configured for this database. Verification failure
-- (bad signature, expired, caveat refused, missing discharge) returns FALSE.
CREATE FUNCTION dregg_cap_admits(
    token    text,
    action   text,
    resource text,
    now      bigint
) RETURNS boolean
  IMMUTABLE PARALLEL SAFE STRICT;   -- STRICT: NULL token ⇒ NULL ⇒ deny

-- Same decision, but raises a NOTICE / returns the human-readable Refusal
-- reason. For debugging policies and for audit logging.
CREATE FUNCTION dregg_cap_explain(
    token    text,
    action   text,
    resource text,
    now      bigint
) RETURNS text IMMUTABLE PARALLEL SAFE;

-- The confined subject (agent identity) the token names, or NULL if the
-- token does not verify. Useful for `actor = dregg_cap_subject(...)` joins
-- and for writing the actor into audit columns.
CREATE FUNCTION dregg_cap_subject(token text) RETURNS text
  IMMUTABLE PARALLEL SAFE;

-- Convenience that reads the session GUC so policies stay terse.
-- `dregg_admits('read', id::text)` == dregg_cap_admits(current_setting('dregg.token', true),
--                                       'read', id::text, extract(epoch from now())::bigint)
CREATE FUNCTION dregg_admits(action text, resource text) RETURNS boolean
  STABLE PARALLEL SAFE;             -- STABLE: reads now() and the session GUC
```

Volatility classification matters for planner behaviour and per-row cost
(§6): `dregg_cap_admits` is `IMMUTABLE` (pure over its four arguments — the
issuer key is a fixed extension config, treated as a constant for a given
database), so the planner can hoist and cache it when the arguments are
constant within a scan. `dregg_admits` is `STABLE` because it reads `now()` and
the session GUC.

Optional **mint/attenuate helpers** (so an application can issue and narrow
tokens without leaving SQL — useful for row-scoped sub-tokens):

```sql
-- Issue a credential carrying caveats encoded as a JSON array of Pred objects.
-- The JSON is the serde-default encoding of dregg_auth::credential::Pred:
-- PascalCase variant names, e.g.:
--   [{"AttrEq":{"key":"action","value":"read"}},
--    {"AttrPrefix":{"key":"resource","prefix":"org/42/"}},
--    {"NotAfter":{"at":2000}}]
-- Other variants: NotBefore, Within, AllOf, AnyOf, Not, "True", "False".
-- The issuer private key is read from the SUPERUSER-ONLY dregg.issuer_privkey GUC;
-- this function is SECURITY DEFINER and only callable by the role the DBA grants.
CREATE FUNCTION dregg_mint(subject text, caveats jsonb, until bigint) RETURNS text
  SECURITY DEFINER;

-- Attenuate a presented token by appending caveats — never widening.
-- IMMUTABLE: no issuer key needed; the token holder may attenuate freely.
CREATE FUNCTION dregg_attenuate(token text, caveats jsonb) RETURNS text
  IMMUTABLE PARALLEL SAFE STRICT;

-- TRUE iff the credential has NOT been revoked in the backend-local registry
-- (populated by dregg_revoke). Use as:
--   USING (dregg_admits(...) AND dregg_cap_not_revoked(current_setting('dregg.token',true)))
-- for instant-revocation semantics (docs §3.4 tier 2). STABLE.
CREATE FUNCTION dregg_cap_not_revoked(token text) RETURNS boolean
  STABLE PARALLEL SAFE STRICT;

-- The per-issuance nonce hex of a credential (root + all its attenuated children
-- carry the same nonce, so revoking by nonce covers the whole family). NULL if
-- the token does not decode. HORIZONLOG: currently returns NULL pending a
-- dregg-auth Credential::nonce() public accessor; use dregg_cap_id for per-token
-- revocation in the meantime.
CREATE FUNCTION dregg_cap_nonce(token text) RETURNS text
  IMMUTABLE PARALLEL SAFE;
```

`dregg_attenuate` is the SQL face of `Credential::attenuate`: it can only narrow,
and the proof `attenuate_subset` is the guarantee that the SQL boundary cannot
amplify. Minting is a privileged operation (holds the issuer secret) and is the
one function that is `SECURITY DEFINER` and role-gated.

### 2.2 Worked RLS policies

A documents table, gated so a token admits a row only if it admits `read` on
that document's id:

```sql
ALTER TABLE documents ENABLE ROW LEVEL SECURITY;

CREATE POLICY cap_read ON documents
  FOR SELECT
  USING (
    dregg_cap_admits(
      current_setting('dregg.token', true),   -- the presented credential
      'read',
      id::text,                                -- the resource being gated
      extract(epoch from now())::bigint        -- the verifier clock
    )
  );
```

Or, with the convenience wrapper:

```sql
CREATE POLICY cap_read ON documents
  FOR SELECT USING (dregg_admits('read', id::text));
```

The **write path** uses the `WITH CHECK` analogue, so a token must admit
`write` (or `create`/`update`/`delete`) on the row being produced:

```sql
CREATE POLICY cap_write ON documents
  FOR UPDATE
  USING       (dregg_admits('write', id::text))   -- which existing rows may be targeted
  WITH CHECK  (dregg_admits('write', id::text));   -- and the post-image must still be admitted

CREATE POLICY cap_insert ON documents
  FOR INSERT
  WITH CHECK  (dregg_admits('create', id::text));

CREATE POLICY cap_delete ON documents
  FOR DELETE
  USING       (dregg_admits('delete', id::text));
```

Resource scoping is not limited to a single id. Because `dregg-auth` has a
**prefix caveat** (`Pred::AttrPrefix`), a token can be confined to a namespace
of rows — e.g. a token admitting `read` on any resource under `org/42/` —
and the policy passes `id::text` (or a path column) as the resource. The
prefix containment is decided inside `dregg-auth`, not in SQL.

### 2.3 The request lifecycle

```
   client                        postgres session                 pg-dregg / dregg-auth
   ──────                        ────────────────                 ─────────────────────
   present dga1_… token  ──────▶ SET dregg.token = 'dga1_…'
                                 (or set_config, or a
                                  connection-pool hook)

   SELECT * FROM documents ────▶ planner attaches RLS policy
                                 cap_read to the scan
                                   │
                                   │  for each candidate row:
                                   ▼
                                 dregg_admits('read', id) ───────▶ Credential::decode(token)
                                                                   Credential::verify(issuer_pk, ctx)
                                                                     ctx = { clock: now,
                                                                             attr action=read,
                                                                             attr resource=id }
                                   ◀─────────────────────────────  Ok(())  ⇒ row visible
                                                                   Err(Refusal) ⇒ row filtered
   rows admitted by the token ◀── only the admitted rows return
```

The token reaches the policy through a **session GUC**, `dregg.token`. Three
ways to set it, in increasing transparency to the app:

1. **Explicit** — the app runs `SELECT set_config('dregg.token', $1, false)`
   (or `SET dregg.token = …`) right after acquiring the connection, before any
   gated query. `set_config(..., false)` makes it session-scoped;
   `set_config(..., true)` makes it transaction-local, which is the safer
   default for a pooled connection (it resets at `COMMIT`/`ROLLBACK`).
2. **Connection-pool hook** — a pgbouncer/pgcat `SET` injected from the
   authenticated principal, the same shape Supabase uses for `request.jwt.*`.
3. **PostgREST-style JWT swap** — a thin gateway verifies the bearer
   credential once, then opens the postgres connection with the token in a
   transaction-local GUC. (Here the credential is the bearer token *itself*,
   not a JWT carrying claims; the policy re-verifies it, so the gateway is not
   trusted for the authorization decision, only for transport.)

A namespaced GUC like `dregg.token` does **not** require pre-registration in
postgres (any setting with a `.` is accepted as a "custom" placeholder), so the
extension does not need a shared-library `define_string_guc` for the token to
flow. Registering it is still worthwhile to attach `GUC_NO_SHOW_ALL` /
`GUC_NOT_WHILE_SEC_REST` flags (so the token never prints in `SHOW ALL` and
cannot be set inside a `SECURITY DEFINER`-restricted context) — pgrx exposes
this via `GucRegistry::define_string_guc` with `GucContext::Userset` and a
`GucFlags` set (see `pgrx/src/guc.rs`).

---

## 3. The dregg-auth integration

`pg-dregg` is a thin marshalling shell; **all** authorization logic is
`dregg-auth`. The mapping, function by function:

### 3.1 Which API backs each SQL function

The `credential` module is the backend (not the biscuit `Grant`/`Token`
wedge), because it is the one with **resource-scoped caveats and an explicit
context** — exactly what per-row RLS needs:

| SQL function | dregg-auth call | notes |
|---|---|---|
| `dregg_cap_admits(token, action, resource, now)` | `credential::Credential::decode(token)?` then `.verify(&issuer_pk, &ctx)` where `ctx = Context::new().at(now).attr("action", action).attr("resource", resource)`; `Ok(())` ⇒ `true`, `Err(_)` ⇒ `false` | the whole decision; fail-closed |
| `dregg_cap_explain(...)` | same, but return `Err(Refusal).to_string()` (the `Refusal` `Display` names the first violated requirement) | the explain discipline surfaced at the SQL boundary |
| `dregg_cap_subject(token)` | decode, verify, then read the subject caveat / attribute the mint convention puts in block 0; `None` ⇒ NULL | for `actor`-column joins and audit |
| `dregg_attenuate(token, caveats)` | `Credential::decode(token)?.attenuate(parse_caveats(caveats)).encode()` | narrowing only; `attenuate_subset` is the no-amplify guarantee |
| `dregg_mint(subject, caveats, until)` | `RootKey::from_seed(secret).mint([... caveats, NotAfter{until}])` `.encode()` | privileged; secret from a superuser GUC |
| `dregg_cap_not_revoked(token)` | `!is_revoked(cap_id(token))` against the backend-local revocation set | STABLE (revocation set can change between statements); optional opt-in tier 2 (§3.4) |
| `dregg_cap_nonce(token)` | `Credential::nonce()` hex — pending `dregg-auth` public accessor; returns NULL today | IMMUTABLE; for family revocation (root + all children share the same nonce); see HORIZONLOG |

The biscuit `Token`/`verify_offline` path (`dregg-auth/src/lib.rs`) remains
available for a **tool-gate** profile (a token confined to *tools* rather than
*resources*) — e.g. gating which postgres *functions* an agent may call rather
than which rows it may read. The `credential` path is the row-gating default;
the biscuit path is the function-gating option. They share the crate and the
issuer-key configuration.

### 3.2 Marshalling across the SQL boundary

Everything dregg-auth needs crosses as text and bigint:

- **Token** — the `dga1_…` (credential) or `eb2_…` (biscuit) **string**,
  passed as SQL `text`. No `bytea` is required: the wire form is already
  header-safe base64url. `pgrx` maps SQL `text` ⇄ Rust `&str`/`String`
  directly.
- **action / resource** — SQL `text` ⇄ `&str`, bound into the `Context` as
  attributes.
- **now** — SQL `bigint` ⇄ `i64` ⇄ `u64` for the credential clock. (The
  credential clock is `u64`; `pg-dregg` rejects a negative `now` as a refusal
  rather than wrapping.)
- **issuer public key** — **not** a per-call argument. It is the database's
  trust root, read once from extension configuration (§3.3) and cached in a
  `OnceCell` for the backend process. Passing it per-call would invite a
  policy author to verify against an attacker-chosen key.
- **caveats JSON** (mint/attenuate only) — SQL `jsonb` ⇄ the serde-default
  encoding of `dregg_auth::credential::Pred` (PascalCase variant names — e.g.
  `{"NotAfter":{"at":2000}}`, `{"AttrPrefix":{"key":"resource","prefix":"org/42/"}}`,
  `{"AllOf":[…]}`). The DSL is the `Pred` algebra; nothing new is invented.
  **Note:** variant names are PascalCase (no `rename_all` on the Rust enum), so
  `AttrEq` not `attr_eq`, `NotAfter` not `not_after`, etc.

### 3.3 The offline-verify model (issuer key as extension config)

Verification needs only the issuer **public key**. `pg-dregg` reads it from a
custom GUC, set in `postgresql.conf` or per-database:

```
# postgresql.conf
dregg.issuer_pubkey = 'b3f1…<64 hex>'    # the Root/RootKey public key, publishable
```

The extension loads it at `_PG_init` (or lazily on first call) into a
process-local `OnceCell<PublicKey>` via `credential::PublicKey::from_hex`. A
malformed or absent key makes every `dregg_cap_admits` **deny** (fail-closed),
with `dregg_cap_explain` reporting "no issuer key configured". Because the
public key is safe to publish, this GUC is `GucContext::Sighup` (settable by
the DBA, visible) — distinct from the *private* key, which only `dregg_mint`
touches and which lives in a `Suset`/superuser-only, `NO_SHOW_ALL` GUC (or,
better, is never placed in postgres at all — minting happens out-of-database
and only public verification lives in pg).

Multiple issuers are supported by a keyed variant
(`dregg_cap_admits_under(token, pubkey_hex, …)`) or by a small
`dregg.issuer_pubkeys` map; the single-issuer GUC is the common case.

### 3.4 Revocation handling

`dregg-auth` is deliberately **revocation-free at the token layer**: its
dependency set excludes `dregg-token`'s `rand-deps` feature, where the
`RevocationRegistry` lives (`token/src/revocation.rs`). This keeps the offline
verifier pure. Revocation is therefore handled by the deployment, with three
escalating options:

1. **Short TTLs as the revocation horizon (default).** Every token carries a
   `NotAfter` caveat; the maximum staleness of an authorization is the token
   lifetime. A 5-minute token means revocation takes effect within 5 minutes
   with zero infrastructure. This is the recommended baseline and matches the
   "tokens are cheap, mint often" discipline.
2. **A revocation-root check inside the policy.** The provider runs a
   `RevocationRegistry` (out of database) and publishes its signed Merkle root.
   `pg-dregg` adds `dregg_cap_not_revoked(token)` backed by a
   non-membership-proof check, or — simpler — the app maintains a
   `revoked_nonces` table and the policy adds
   `AND NOT EXISTS (SELECT 1 FROM revoked_nonces r WHERE r.nonce = dregg_cap_nonce(token))`.
   This is a synchronous DB check, so it trades a join for instant revocation.
3. **Foreground registry call (FFI tier only).** If the maximal-assurance FFI
   tier (§4) is deployed, the node's revocation path can be consulted; this is
   the heaviest and is out of scope for the embeddable layer.

The honest statement: the embeddable `pg-dregg` layer's *default* revocation
semantics are **bounded-staleness via TTL**, not instant. Instant revocation is
the opt-in (2)/(3) tiers. This is the same tradeoff every offline-capability
system makes, and it is stated plainly rather than papered over.

---

## 4. The assurance story

**What is verified, and where the assurance comes from.**

The authorization *semantics* `pg-dregg` enforces — admit = the meet of all
caveats, attenuation can only narrow, unbound/cross-bound discharges are
rejected, fail-closed under negation — are the machine-checked theorems of
`metatheory/Dregg2/Authority/` (`Caveat.lean` `Token.admits`,
`attenuate_subset`, `BiscuitGraph` forged/stripped-block rejection,
`MacaroonDischarge.unbound_discharge_rejected` /
`binding_not_replayable_to_other_root`, `PredAlgebra` Boolean laws,
`TemporalAlgebra` window = meet). The `dregg-auth/src/credential/` module is the
Rust embodiment of those theorems, with each type's doc comment naming its Lean
counterpart, and the assurance link between the Lean and the Rust is the
**differential** the dregg tree already runs (the model-finds-the-bug loop). The
`pg-dregg` shell adds no authorization logic; it marshals text/bigint into the
already-assured `Credential::verify`.

**Be precise about the boundary.** What the differential gives is: *the Rust
`dregg-auth` decision agrees with the proved Lean semantics.* What `pg-dregg`
adds on top — the GUC plumbing, the planner's per-row invocation, the
SECURITY-DEFINER minting gate — is **ordinary extension code, not formally
verified.** The honest claim is therefore:

> The *capability decision* a `pg-dregg` policy makes is the verified dregg
> decision; the *integration that delivers the token to that decision* is
> conventional, audited postgres-extension code.

We do not claim "the postgres layer is formally verified." We claim the
authorization core it calls is, with a named differential as the anchor, and we
name the unverified seam (the GUC/plumbing) explicitly.

### The lightweight-Rust vs FFI-Lean tradeoff

| | **Lightweight `dregg-auth`** (recommended) | **FFI the real Lean gate** |
|---|---|---|
| What runs in the backend | pure Rust: ed25519 + blake3 + postcard; no Lean runtime | `libdregg_lean.a` (several MB) + a Lean runtime in every backend process |
| Assurance | the Lean↔Rust differential on the proved `gateOK`/caveat semantics | the *actual* verified gate (`dregg_exec_full_forest_auth`, `dregg_captp_validate_handoff`) runs |
| Embeddable / offline | yes — the whole point of `dregg-auth` (`cargo tree -i dregg-circuit -p dregg-auth` is empty) | no — links a Lean runtime, breaks the "no node, no wallet" story, heavy per-backend |
| Per-row cost | a few µs (signature-chain verify) | dominated by Lean runtime init + a heavier gate |
| Deployment | one `cdylib`, copy + `CREATE EXTENSION` | build + ship + load a multi-MB Lean static lib; backend memory blows up |

**Recommendation: ship the lightweight `dregg-auth` core for the embeddable RLS
layer.** It is exactly what `dregg-auth` was built to be — offline, embeddable,
dependency-tight — and the Lean differential is a strong, already-existing
assurance anchor for the authorization semantics. The FFI-Lean path is recorded
as an **optional maximal-assurance tier** for a deployment that (a) already runs
a dregg node, (b) needs the literal verified gate in the loop, and (c) can pay
the per-backend Lean-runtime cost — but it is *not* the default, and forcing it
would forfeit the embeddability that makes this product attractive.

---

## 5. The prototype plan

### Milestone 1 — the smallest thing that demonstrates the thesis

**Deliverable:** one pgrx function `dregg_cap_admits` + one RLS-gated table + a
`cargo pgrx test` proving that an **attenuated** token is correctly *narrowed*
at the SQL boundary (the no-amplify property visible through postgres).

The decisive test:

```rust
// cargo pgrx test
#[pg_test]
fn attenuated_token_is_narrowed_at_the_sql_boundary() {
    // Mint a token admitting read on any resource under "org/42/", until clock 2000.
    // Attenuate it to ONLY "org/42/public/" before handing to the session.
    // Then, via SQL:
    //   - dregg_cap_admits(narrowed, 'read', 'org/42/public/doc1', 1000) is TRUE
    //   - dregg_cap_admits(narrowed, 'read', 'org/42/private/doc9', 1000) is FALSE
    //     (the parent admitted it; the attenuated child does not — narrowing held)
    //   - dregg_cap_admits(narrowed, 'read', 'org/42/public/doc1', 3000) is FALSE
    //     (past the NotAfter expiry)
    // And through a real RLS-gated table:
    //   SET dregg.token = <narrowed>;
    //   SELECT count(*) FROM documents;   -- returns only the org/42/public rows
}
```

This single test exercises: decode → verify, the resource caveat, the temporal
caveat, **and** the attenuation no-amplify property — all observed *through the
SQL boundary*, which is the whole proof-of-concept.

### Crate shape — `pg-dregg/`

```
pg-dregg/
  Cargo.toml          # [lib] crate-type = ["cdylib", "lib"]; pgrx + dregg-auth
  src/lib.rs          # #[pg_extern] dregg_cap_admits / dregg_cap_explain /
                      #   dregg_cap_subject / dregg_admits; issuer-key OnceCell;
                      #   the caveat JSON DSL ⇄ Pred mapping
  sql/                # bootstrap SQL: the CREATE POLICY examples, a demo table
  pg-dregg.control    # extension control file (generated by pgrx)
```

**Pinning.** `pgrx = "0.17"` (supports `pg13`–`pg18` via the `pg13`…`pg18`
features). The **primary target is PostgreSQL 18** (the current release; see
`docs/PG-DREGG-PG18.md` for the pg18 features the mirror leverages — virtual
generated columns, `RETURNING old/new`, `uuidv7`, OAuth, async I/O); pg13–pg17
remain selectable for older deployments. `dregg-auth` is a path dependency
(`{ path = "../dregg-auth" }`), default features — it is already circuit-free,
so no feature surgery is needed. (The block below is the original M1-planning
sketch; the live `Cargo.toml` keeps `default = []` so the postgres-free core
builds under plain `cargo test`, and selects a pg ABI — `pg17` primary — on the
`cargo pgrx` command line.)

```toml
# pg-dregg/Cargo.toml (sketch)
[lib]
crate-type = ["cdylib", "lib"]

[features]
default = ["pg16"]
pg13 = ["pgrx/pg13", "pgrx-tests/pg13"]
pg16 = ["pgrx/pg16", "pgrx-tests/pg16"]
pg_test = []

[dependencies]
pgrx = "0.17"
dregg-auth = { path = "../dregg-auth" }
serde = { workspace = true }
serde_json = { workspace = true }

[dev-dependencies]
pgrx-tests = "0.17"
```

**Build / test commands** (NOT run in this lane — they invoke `cargo pgrx`,
which compiles postgres bindings and contends for `./target`):

```
cargo install cargo-pgrx --version 0.17.0
cargo pgrx init --pg18 $(brew --prefix postgresql@18)/bin/pg_config  # primary target
cargo pgrx test pg18        # runs the #[pg_test]s against the managed pg18
cargo pgrx run  pg18        # opens psql with the extension loaded
# (pg13–pg17 remain available: cargo pgrx test pg17, etc.)
```

`pg-dregg/` should likely be added to the **workspace `exclude` list**, not
`members` — a `cdylib` with a `cargo-pgrx`-managed test harness does not want
to participate in `cargo check --workspace`, and keeping it excluded protects
the ten concurrent lanes sharing `./target` from the pgrx build's postgres
bindings. (This mirrors how `wasm`/`sdk-py` are excluded.)

### Out of scope for milestone 1

- mint/attenuate SQL helpers (`dregg_mint`/`dregg_attenuate`) — the test can
  mint in Rust before the SQL boundary;
- third-party discharge through SQL (the `Context::discharge` plumbing);
- the revocation-root check;
- multi-issuer key maps;
- the FFI-Lean tier;
- the read-side query surface (§7);
- performance work beyond noting the volatility classification.

Milestone 1 is intentionally one function, one table, one test — the thesis in
the smallest verifiable form.

---

## 6. Risks & open questions

- **Per-row function-call cost on large scans.** RLS evaluates the `USING`
  predicate **once per candidate row**. A signature-chain verify is a few µs,
  but on a 10M-row sequential scan that is seconds of pure verification.
  Mitigations, in order: (a) classify `dregg_cap_admits` `IMMUTABLE` so the
  planner caches it when arguments are constant within the scan; (b) cache the
  *decoded+verified* credential per `(token-string)` in a backend-local
  `OnceCell`/LRU so only the per-row caveat *evaluation* runs per row, not the
  whole signature-chain verify (decode/verify the chain once per session, then
  each row only re-evaluates `Pred` over the row's resource — turning the
  per-row cost from ed25519 into a string compare); (c) structure policies so a
  cheap SQL predicate (a tenant column) pre-filters before `dregg_admits`
  runs (postgres evaluates RLS predicates after, but a partial index + a `USING
  (tenant = … AND dregg_admits(…))` lets the index cut the candidate set
  first); (d) for prefix-scoped tokens, push the prefix into a SQL `LIKE` the
  planner can index, with `dregg_admits` as the exact backstop. Mitigation (b)
  is the important one and belongs in milestone 2.

- **Token-in-session-var security model.** The token is a **bearer
  credential** in a session GUC. Risks: it can appear in `SHOW ALL`, in
  `pg_settings`, in log lines, and persists on a pooled connection if not
  reset. Mitigations: register the GUC with `GUC_NO_SHOW_ALL`; prefer
  *transaction-local* `set_config(..., true)` so it clears at transaction end
  (critical for connection poolers); never log the GUC; and treat the GUC value
  as secret in any audit pipeline. The bearer nature is inherent to capability
  tokens — the GUC is just the transport — but the operational hygiene must be
  documented loudly.

- **FFI-tier deployment cost.** Recorded in §4; the open decision is whether to
  even offer it in v1 or defer it entirely. Recommendation: defer; the
  lightweight tier is the product.

- **Coexistence with the in-flight VK rotation.** `pg-dregg` depends on
  `dregg-auth`, which has **no circuit/VK edge whatsoever** (the empty
  `cargo tree -i dregg-circuit` is the established fact). The VK rotation does
  not touch this layer. The only contact point is `./target` contention during
  a `cargo pgrx` build — hence the `exclude`-from-workspace recommendation, so
  pgrx builds never collide with the rotation lanes' workspace builds.

- **Clock unit agreement.** `dregg-auth`'s credential clock is a single
  monotone `u64` (unix seconds *or* block height — mint and verify must agree).
  `pg-dregg` standardizes on **unix seconds** (`extract(epoch from now())`),
  and this must be documented as the deployment's clock contract so minted
  tokens and policies never disagree.

### ember decisions surfaced

1. **Default revocation semantics = bounded-staleness via short TTL**, with
   the synchronous registry check as an opt-in tier. Acceptable, or does the
   product need instant revocation in the default path? (This shapes whether
   `dregg_cap_not_revoked` is milestone-1 or milestone-2.)
2. **Resource-scoped `credential` path as the row-gating default** (vs the
   biscuit tool-gating path). Confirm `credential` is the surface to lead with;
   the biscuit path stays as the function-gating option.
3. **Offer the FFI-Lean tier in v1, or defer it?** Recommendation: defer.
4. **`pg-dregg/` excluded from the workspace** (own pgrx build, protects the
   shared `./target`) — confirm this is the desired layout vs a member.

---

## 7. Secondary — the read-side query surface (feasibility note only)

A read-side surface — SQL functions or a foreign-data-wrapper exposing dregg
**cells and receipts** as queryable postgres relations — is a separate, secondary
product from the authz layer and is explicitly *not* part of this proposal's
core. Feasibility, in one paragraph: the `dregg-query` crate already exists
(`dregg-query/src/`) and provides exactly the right primitive — a conjunctive
query evaluator over the receipt fact-base (`created`/`transfer`/`balance`/
`granted`/`revoked`), with a CALM monotonicity grade per query and an MMR
non-omission certificate (`AttestedAnswer`) proving an answer was computed from
exactly the committed receipt range. Surfacing it in postgres is a light lift as
**SQL set-returning functions** (`dregg_receipts(since bigint) RETURNS SETOF
record` backed by `dregg-query`'s evaluator) rather than a full FDW (a FDW's
planner integration is much heavier and buys little when the fact-base is an
append-only log a SRF can stream). The attestation story is the differentiator
over a plain materialized view: a `dregg_receipts` answer can carry its MMR
opening so a downstream consumer verifies non-omission. This is a genuinely nice
secondary surface, but it is independent of, and should not gate, the
authz/RLS layer that is this proposal's thesis.

---

# Part II — making `pg-dregg` first-class: storage, query, execution

§1–§7 are the LANDED M1: dregg capabilities as PostgreSQL RLS (Tier A). They
make postgres a first-class *authorization* surface for dregg. Part II asks the
larger question — *can postgres be a first-class **storage, query, and
execution** surface for dregg, using pg for ALL of it, without weakening one
guarantee?* The answer is **yes, and there is exactly one invariant that makes
it sound.** State the invariant first; every tier below is a way of honouring
it.

## 8. The spine invariant — reads are free SQL, state mutates only through verified turns

> **THE INVARIANT.** Postgres may be dregg's first-class storage and query
> surface *without weakening a single guarantee*, **iff** every row that
> represents dregg state appears **only** as the result of a verified turn
> executed by the real kernel (the embedded Lean executor, or a node) — **never**
> by a bare SQL `INSERT`/`UPDATE`/`DELETE`. Ordinary SQL `SELECT` queries the
> materialized state freely; **writes pass through the verifier.**

This is the whole game. dregg's guarantees — conservation (value is neither
created nor destroyed across a turn), no-amplification (a delegated capability
admits a subset of its grantor's), nullifier-uniqueness (no double-spend),
authenticated state-root evolution (the post-state commitment is the verified
fold of the pre-state and the turn) — are *properties of the executor's
transition function*. They live in the **write path**, not in the bytes at rest.
A `SELECT` cannot violate them; it only observes. A bare `UPDATE cells SET
balance = balance + 1000000` **annihilates all of them at once** — it forges
value, with no turn, no proof, no nullifier, no root update. So:

- **Reads are free.** Any `SELECT`, join, aggregate, window function, recursive
  CTE over the materialized state is sound by construction, because reading
  cannot break an invariant of the transition function. This is what lets
  postgres be a genuinely first-class *query* surface: the full power of SQL,
  RLS-gated by Tier A, with zero new trust.
- **Writes are gated.** A row representing dregg state may enter a table *only*
  as the post-image of a verified turn. The mechanism that enforces this is the
  tier ladder: Tier B *materializes* verified-turn output (the node is the
  writer, SQL is forbidden to write); Tier C makes the *verifier itself* the
  gate (`dregg_verify_turn` in a `CHECK`/trigger — a row cannot exist unless it
  is a verified-turn result); Tier D makes the *executor* a postgres function
  (`dregg_submit_turn` — postgres becomes the kernel and produces the rows
  itself, atomically).

**If you let SQL mutate cells directly, you bypass the executor and the design
is unsound.** Every tier below is therefore measured against this one question:
*does a state row ever exist except as a verified-turn post-image?* When the
answer is "no", postgres is first-class AND sound. The honest failure mode is
naming it loudly: a tier that grants an application `UPDATE` on a state table
has silently re-opened the bypass, and is wrong no matter how convenient.

The tiers:

| Tier | What postgres becomes | Writer of state rows | Verifier in the loop | Status |
|---|---|---|---|---|
| **A** authz | a capability-gated **policy** surface | (app's own tables) | dregg-auth (caps) | **LANDED (M1)** |
| **B** mirror | a first-class **query** surface over dregg state | the **node** (SQL forbidden) | upstream (the node already verified) | proposed **M2** |
| **C** verified store | a **verifying light client, in SQL** | the node, *through* `dregg_verify_turn` | the verifier, in a `CHECK` | proposed **M3** |
| **D** executor-in-pg | **a dregg node** | postgres itself | the embedded Lean executor | **v-future** |

Tiers compose: B's tables are what C gates and D produces. A's RLS gates the
*reads* of all of them.

### 8.1 Circuits and online operation ARE authorized here

A note that reshapes the cost/payoff of the heavier tiers. §4 frames the M1
authz layer's *circuit-free, fully-offline* profile (`cargo tree -i dregg-
circuit -p dregg-auth` is empty) as a virtue — and for **Tier A** it is: a
capability check should not need a proof system or a network. But that circuit-
free property is a *property of Tier A*, **not a design boundary on `pg-dregg`
as a whole.** `pg-dregg` is explicitly authorized to **link the circuit/proof
stack and to operate online** when a tier needs it. That changes the calculus
for Tiers C and D decisively:

- Tier C *wants* the proof **verifier** in the backend — that is not a
  reluctant heavyweight to be avoided, it is the **point** of the verified
  store, and linking it is sanctioned.
- Tier D *wants* the executor — likewise sanctioned where the payoff (postgres
  *is* a dregg node) is wanted.
- `pg-dregg` may therefore depend on the real dregg types and the real verifier
  (and, at Tier D, the executor), not only on the offline `dregg-auth` core.

So read the C/D cost sections below as **"here is what it links and the
operational weight to plan for,"** NOT as "here is why to avoid it." The only
thing the heavier tiers must never trade away is the **spine invariant** — and
linking the verifier/executor *strengthens* it (the gate becomes the real
verifier / the real kernel), never weakens it. The offline profile stays the
**default for Tier A**, because a row-read policy genuinely should not pull a
prover; the online/circuit profile is a first-class, authorized build for the
tiers whose whole job is verified writes and execution.

## 9. Tier B — dregg state as queryable postgres tables

**The proposition.** Materialize the live dregg state — cells, receipts/turns,
the blocklace DAG, capabilities + the delegation graph, the universal-memory
multiset — as real, indexed, RLS-gated SQL tables, so the explorer, analytics,
and app queries are *plain SQL joins* instead of bespoke RPC against a node.
The concrete schema is `pg-dregg/sql/schema-tierB.sql` (a marked DESIGN SKETCH);
this section is its rationale and soundness argument.

### 9.1 The mirror is a projection of an artifact that already exists

The decisive fact: **the node already persists exactly this, in exactly this
shape.** `persist/src/commit_log.rs`'s `CommitRecord` is the authoritative,
append-only, crash-consistent record of every verified turn the node applied —
and it already carries `ordinal · height · block_id · turn_hash · creator ·
receipt_hash · ledger_root · touched_cells: Vec<Cell>`. The commit log writes
the cursor, the per-turn index (receipt-by-hash, turn-by-hash, turn-by-(height,
creator)), and the per-turn cell snapshots **in one redb transaction** with the
ledger-root post-state binding. Tier B is *that record, projected into SQL
tables.* We are not inventing a schema; we are giving the commit log a SQL face:

- `dregg.turns` ⟵ `CommitRecord` (one row per ordinal),
- `dregg.cells` ⟵ `LedgerCheckpoint.cells` + `CommitRecord.touched_cells`
  (latest post-image per cell; `dregg.cell_history` keeps every post-image, which
  is just the cell-by-(id,ordinal) index surfaced),
- `dregg.capabilities` ⟵ each cell's `CapabilitySet` / `CapabilityRef`
  (cell/src/capability.rs) — the delegation graph as edges,
- `dregg.blocks` / `dregg.block_edges` ⟵ `persist/src/blocklace_store.rs` (the
  consensus DAG),
- `dregg.memory` ⟵ the universal-memory multiset (§11).

Every column in the sketch is provenance-tagged to its Rust source so the mirror
is a *faithful* projection.

### 9.2 Mirror, or backend? — the one architectural decision

There are two ways to populate Tier B, and they sit at different points on the
sound↔invasive axis:

**(B1) Postgres as a MIRROR the node writes to (recommended for M2).** The node
keeps redb as its source of truth; a small sink in the commit path (right where
`CommitRecord` is written) upserts the same record into postgres in the same
logical commit. Postgres is a *read replica of verified state.* The spine
invariant holds **trivially**: the only writer is the node's commit path, which
only ever writes verified-turn output, and applications get `SELECT` only.

- *Soundness:* airtight — postgres never decides anything; it reflects what the
  node already verified. The mirror can even re-check each row's `ledger_root`
  chains to the previous (the Tier-C tooth, §10, applied read-only) to detect a
  tampered mirror.
- *Cost:* a dual-write (redb + pg) in the commit path, and an eventual-vs-strict
  consistency choice (write pg in the same redb transaction boundary, or
  async-tail it from the commit log — the commit log is replayable, so an
  async tailer that resumes from `commit_cursor()` is crash-safe and never loses
  a turn).
- *Payoff:* the entire query surface, immediately, at near-zero risk.

**(B2) Postgres as THE node's persist backend (replacing/augmenting redb).** The
node's `PersistentStore` trait is re-implemented over postgres: the commit log,
ledger checkpoints, and indices live in pg tables, and redb is retired or kept
as a cache. Postgres is now the *system of record.*

- *Soundness:* still sound — the same commit-path code writes, the same
  one-transaction atomicity is available (pg is ACID, like redb), and the spine
  invariant is identical (the executor is the only writer). The CommitRecord
  invariants (`commit_cursor() == commit_log.len()`, no torn state, no
  double-apply) port to pg transactions one-for-one.
- *Cost:* a real engineering lift — re-implement `PersistentStore` over `tokio-
  postgres`/`sqlx`, port the crash-consistency proofs' assumptions (redb's
  single-writer fsync boundary ⟶ a pg transaction), and accept a network round-
  trip per commit where redb was in-process. It also couples node availability
  to pg availability.
- *Payoff:* one store, not two; no dual-write skew; the node's durability *is*
  the DBA's postgres backups/replication/PITR — operationally huge.

**Recommendation: B1 for M2** (mirror — fast, airtight, reversible), with B2
recorded as the natural successor once the mirror has proven the schema and the
query surface in production. B1 and B2 share the schema; B2 is "promote the
mirror to the source of truth," not a rewrite of the tables.

### 9.3 Soundness of Tier B

The mirror tables are **read-only to applications** (the `dregg_reader` role gets
`SELECT`, never `INSERT/UPDATE/DELETE`; the only writer is `dregg_kernel`, the
node's commit path). `FORCE ROW LEVEL SECURITY` + `REVOKE … FROM PUBLIC` close
the privilege side. Therefore no application SQL can create a state row — the
spine invariant holds by *construction of the privilege model*, before any
trigger. Reads are RLS-gated by Tier A (§6 of the sketch): the explorer is
literally "the rows your capability admits." Tier B weakens **nothing**: it adds
a query surface over already-verified state and forbids the only operation
(application writes) that could break an invariant.

### 9.4 Tier B verdict: **GREEN**

The artifact already exists (`CommitRecord`), the mirror is a projection, the
soundness is by privilege construction, and the payoff (full SQL over dregg
state, RLS-gated) is large and immediate. **Biggest risk:** mirror *staleness /
skew* under B1 — a crash between the redb commit and the pg write. Mitigated by
tailing the replayable commit log from `commit_cursor()` (crash-safe, exactly-
once) rather than a best-effort dual-write, and by the read-only root-chain
re-check that detects a diverged mirror. This is the M2 milestone.

## 10. Tier C — writes through the verifier (the CHECK tooth)

**The proposition.** Make the *verifier itself* the gate on the state tables, so
that **no row can exist unless it is the result of a verified turn** — enforced
by postgres, not by trusting the writer. This turns Tier B's "the node promises
it only writes verified output" into "postgres *checks* that every write is
verified output." It is the verifying light client, realized as the store.

### 10.1 The gate

A turn arrives as `(envelope, receipt, proof, vk)`. Tier C adds a function

```sql
-- TRUE iff `proof` is a valid proof that applying the turn in `envelope`
-- to the pre-state root produces `receipt` (whose post-state root is
-- receipt.ledger_root), under verification key `vk`. Pure verification:
-- no execution, no Lean executor — just the STARK/PI verifier + the
-- root-binding check (the snapshot.rs `claimed_root` anti-substitution tooth,
-- lifted into SQL).
CREATE FUNCTION dregg_verify_turn(envelope bytea, receipt bytea, proof bytea, vk bytea)
    RETURNS boolean STABLE PARALLEL SAFE;
```

and gates every state write on it. The cleanest shape is a **single
`dregg.commit_log` table whose `INSERT` trigger is the only path to state**, and
whose trigger:

1. verifies `dregg_verify_turn(envelope, receipt, proof, vk)` — else `RAISE`;
2. checks `receipt.prev_root = (SELECT ledger_root FROM dregg.turns ORDER BY
   ordinal DESC LIMIT 1)` — the post-state of turn *N* is the pre-state of *N+1*,
   so the roots **chain** (this is exactly `snapshot.rs`'s `claimed_root`
   binding and `CommitRecord`'s "ledger_root binds the record to a concrete
   post-state");
3. derives the `dregg.cells` / `dregg.memory` / `dregg.capabilities` post-images
   from the verified receipt and upserts them **in the same transaction**.

```sql
CREATE FUNCTION dregg.apply_verified_turn() RETURNS trigger AS $$
BEGIN
  IF NOT dregg_verify_turn(NEW.envelope, NEW.receipt, NEW.proof, NEW.vk) THEN
    RAISE EXCEPTION 'dregg: turn proof does not verify — refused';
  END IF;
  IF NEW.prev_root IS DISTINCT FROM
       (SELECT ledger_root FROM dregg.turns ORDER BY ordinal DESC LIMIT 1) THEN
    RAISE EXCEPTION 'dregg: turn does not chain to the head root — refused';
  END IF;
  -- derive + upsert cells/memory/caps from the verified receipt (SECURITY DEFINER)
  PERFORM dregg.materialize_post_state(NEW.receipt);
  RETURN NEW;
END $$ LANGUAGE plpgsql SECURITY DEFINER;

CREATE TRIGGER verify_before_apply BEFORE INSERT ON dregg.commit_log
  FOR EACH ROW EXECUTE FUNCTION dregg.apply_verified_turn();
```

Now the spine invariant is enforced by the **database engine**: a row in
`dregg.cells` exists *iff* some `dregg.commit_log` insert carried a turn whose
proof verified and whose root chained. A forged `INSERT INTO dregg.cells`
doesn't exist as a path (no write grant); the only door is `dregg.commit_log`,
and that door runs the verifier. This is "a verifying light client, in SQL,
made into the store" — precisely the project's framing.

### 10.2 What it links (and the authorized profile)

Tier A/B link only `dregg-auth` (pure Rust, no circuit). **Tier C links the
proof verifier — and that is sanctioned** (§8.1): the verified store's whole job
is to run the real verifier on the write path. The recommended shape:

- **(C-embed) embed the verifier in the backend (recommended).** Link the
  STARK/PI verifier — the light-client checker — into the extension. Built
  Lean-free with the `no-lean-link` profile (the verifier is verification-only —
  no executor, no Lean runtime — so it is far lighter than Tier D, even though it
  is heavier than `dregg-auth`: plonky3 + the PI checker, multi-MB). This is the
  authorized, first-class form: the backend itself verifies every turn. The
  `pg-dregg` crate gains a `tier-c` feature that pulls the verifier crate; the
  Tier A build stays circuit-free by default, and the verified-store build opts
  in.
- **(C-callout) call out to a node's verify endpoint (the light alternative).**
  `dregg_verify_turn` becomes a foreign call (a node RPC / a background worker)
  to a co-located node that runs the real verifier. Keeps the backend light at
  the cost of a synchronous dependency and a trust boundary (the callout target
  must be the real verifier, co-located and authenticated). Use this only where
  embedding the verifier is genuinely unwanted; C-embed is the first-class path.

#### 10.2.1 The proof gate as a RANGE-attest SRF (the shape, and the circuit-link seam)

The per-row `dregg_verify_turn` is the *structural* chain tooth; the *proof*
gate is a different shape, because the IVC artifact is whole-chain by
construction. `circuit::ivc_turn_chain::verify_turn_chain_recursive` checks ONE
succinct recursive proof attesting that **all K finalized turns in a receipt
RANGE executed correctly and the root chain advanced** from `genesis_root` to
`final_root` — verifier cost independent of K. Its natural SQL shape is therefore
a **set-returning function over a range**, not a per-row boolean:

```sql
-- Verify ONE whole-chain proof for the window [lo, hi] against the published VK
-- anchor; on success return one row per attested ordinal (read from dregg.turns),
-- each tagged proof_attested = true. Fail-closed: a refusal returns ZERO rows.
dregg_attest_range(proof bytea, vk_anchor bytea, lo bigint, hi bigint)
  RETURNS SETOF (ordinal bigint, prev_root bytea, ledger_root bytea, proof_attested bool);
dregg_attest_explain(proof bytea, vk_anchor bytea, lo bigint, hi bigint) RETURNS text;  -- the verdict reason
```

A consumer JOINs it against `dregg.turns` to mark the proof-attested prefix —
distinct from the merely chain-consistent rows the structural tooth admits:

```sql
SELECT t.ordinal, (a.proof_attested IS TRUE) AS proof_attested
FROM dregg.turns t
LEFT JOIN dregg_attest_range(:proof, :vk, 0, 100) a USING (ordinal)
ORDER BY t.ordinal;
```

The SRF *shape* is **built and `cargo test`-proven** in `pg-dregg/src/attest.rs`
(the request/verdict types, the **anti-overclaim tooth** — a proof for K turns
cannot attest a window of more than K — and the fail-closed expansion to rows),
written ONCE against a single circuit-link seam, `attest::verify_serialized_proof`.

**The circuit-link, by feature.** `verify_turn_chain_recursive` takes an
*in-memory* `WholeChainProof`, whose `root.1` (`Rc<CircuitProverData>`) is
prover-only and not serde — but the verifier never reads it. The
**verify-sufficient subset** (the root `BatchStarkProof`, the chain-binding
`Proof`, the four publics) **is** serde, so it crosses the SQL boundary as
`bytea`. With `tier-c` **OFF** (default) the circuit is not linked and the seam
`attest::verify_serialized_proof` FAILS CLOSED — it attests nothing — which is
the §10.3 safe direction. With `tier-c` **ON** the seam decodes the transport's
proof blobs and runs the real cryptographic teeth. The three steps:

- **S1 (LANDED)** — `circuit::ivc_turn_chain` carries the versioned envelope
  `WholeChainProofBytes` + `WholeChainProof::to_bytes()` and the parts/blob
  verifiers `verify_turn_chain_recursive_from_parts` /
  `verify_turn_chain_recursive_from_blobs` (a split of `verify_turn_chain_recursive`'s
  body, which already reads only the verify-sufficient subset). The transport
  `attest::SerializedWholeChainProof` carries the same two postcard blobs + publics.
- **S2** — the node-side PRODUCER: when finality advances, fold the new finalized
  turns (`prove_turn_chain_recursive` / the `fold_two_turns` accumulator) and
  write the serialized proof + its window bounds into a `dregg.turn_proofs(lo,
  hi, genesis_root, final_root, proof bytea, vk)` table the SRF reads.
- **S3 (LANDED)** — the `tier-c` feature pulls `dregg-circuit` **Lean-free**
  (`--features recursion`: the recursion verifier, NO executor, NO Lean runtime —
  §8.1 authorizes the circuit link for Tier C), and `attest::verify_serialized_proof`
  decodes the transport blobs and calls `verify_turn_chain_recursive_from_blobs`
  against the anchor.

S2 touches the node and is therefore the post-flip half of M3 (the structural
gate + this SRF shape + the now-real circuit link are the pg-side halves that
ship); S1/S3 are circuit-side and Lean-free.

### 10.3 Soundness, and the honest failure mode

Done right, Tier C is the *strongest* sound tier short of D: the database refuses
to hold any state that is not a verified-turn post-image, and the root-chaining
makes the table a hash-chain a light client could itself check. The honest
failure mode to forbid loudly: **if `dregg_verify_turn` is stubbed to `TRUE`
(or the trigger is dropped, or an app is granted a direct write), the gate is
gone and the store silently accepts forged state.** So Tier C's correctness rests
on (a) the verifier being the *real* verifier (named differential, as in §4),
and (b) the trigger + privilege lockdown being audited as load-bearing. A
stubbed verifier here is the same disease as a vacuous spec: a labeled gate that
doesn't gate.

### 10.4 Tier C verdict: **GREEN/YELLOW** (GREEN on intent, YELLOW on the carve-out)

Sound and high-value, and — now that linking the verifier is authorized
(§8.1) — the *right* shape rather than a reluctant one. It is GREEN on intent
(embed the real verifier; the database refuses any non-verified state) and
YELLOW only on the engineering of carving the verifier out Lean-free behind the
`tier-c` feature (real work, but bounded — the light client already isolates the
checker from the executor). **Biggest risk:** the verifier carve-out is more
Lean-entangled than the light-client framing suggests, in which case C-callout
(verify via a co-located node) preserves soundness while the carve-out matures.
Recommended as **M3**, after the B mirror is in production and the schema is
proven.

## 11. Tier D — the executor as a postgres function (the AWESOME endgame)

**The proposition.** Run the **embedded kernel inside the backend**, so

```sql
SELECT dregg_submit_turn(envelope);   -- returns the receipt
```

*executes* the turn — the real verified executor produces the post-state — and
the cells/memory/caps tables update **atomically in the same SQL transaction.**
At this point **postgres IS a dregg node**: a developer's existing postgres is
their dregg node; turns are submitted as SQL; state is queried as SQL; the whole
thing is one ACID transaction.

### 11.1 What it links (authorized weight to plan for)

Tier D embeds the **verified Lean executor** — the `state_producer = "lean"`
path the node already runs (`node/src/api.rs`: `DREGG_LEAN_PRODUCER`, the SWAP
boundary; `dregg_exec_full_forest_auth`). Linking it is authorized (§8.1); the
weight to plan for is the multi-MB Lean static lib (`libdregg_lean.a`) plus a
Lean runtime in **every backend process** — the master-interface-build weight,
in pg's per-connection process model. So backend memory and startup grow, and
the Lean runtime must be safe under pg's `fork()`-per-backend and error model.
That last point is the *real* gate on Tier D, and it is a technical hazard, not
a policy one (§11.3): authorizing the link does not make pg's `setjmp`/`longjmp`
error path automatically safe for a Lean runtime mid-stack.

### 11.2 Why it is still sound (and uniquely powerful)

The executor inside the backend is *the same verified executor the node runs* —
the one whose transition function carries conservation / no-amplification /
nullifier-uniqueness (the machine-checked guarantees in
`metatheory/Dregg2/`). So `dregg_submit_turn` produces *only* verified post-
state, by definition; the spine invariant holds because the writer is literally
the kernel. The unique win over Tier C: **atomicity with application data.** A
turn and the application's own (non-dregg) rows commit or roll back *together*,
in one transaction — something neither a separate node nor Tier C's mirror can
offer. `BEGIN; SELECT dregg_submit_turn(pay_invoice); UPDATE invoices SET paid =
true; COMMIT;` is atomic across the kernel and the app. That is the AWESOME
endgame: dregg state and app state share a transaction.

### 11.3 Tier D verdict: **YELLOW (authorized; gated on the pg/Lean process model), the north star**

The verdict moves up from RED now that embedding the executor is sanctioned
(§8.1): the blocker is no longer "is this an allowed thing to link" but the one
genuine technical hazard. It is the *most* sound tier — the kernel itself is the
writer — and the only thing standing between it and GREEN is whether the Lean
runtime is robust under postgres's per-backend `fork()` / error model (pg uses
`setjmp`/`longjmp` for error handling; a Lean runtime mid-stack is a hazard that
needs a spike to clear). **Biggest risk: exactly that** — pg's longjmp error
unwinding vs the Lean runtime's stack. Recommendation: pursue after B+C are in
production, *front-loaded by a small spike* that links the executor into one
backend and hammers the error path; if the spike is clean, Tier D is GREEN and
the "your postgres IS your dregg node, atomic with your app data" payoff is
real. A lighter intermediate that sidesteps the hazard entirely is
**D-sidecar**:
`dregg_submit_turn` hands the envelope to a co-located node over a unix socket
and the node executes; you lose single-transaction atomicity but keep the SQL
submit ergonomics without linking Lean into the backend — a sound, much cheaper
75% of the payoff, and a sensible stepping stone.

### 11.4 The write path today — the outbox slice (landed) and the M3 drainer

The first-class bidirectional piece — *a pg-user submits a verified turn FROM
postgres* — does not need Tier D's in-backend Lean to begin. The realizable
slice, **landed**, is the **submit outbox** (`pg_dregg::mirror::ddl::write_outbox`,
installed by `dregg_install_write_outbox()`):

- **`dregg.submit_turn(signed_turn bytea, agent bytea) -> uuid`** (extension
  function) enqueues a signed turn into `dregg.submit_queue` and returns the
  submission id. It runs as the *calling* role (NOT `SECURITY DEFINER`), so the
  enqueue is gated by the **`submit_gate` RLS policy**
  `WITH CHECK (dregg_admits('submit', encode(agent,'hex')))`: a role may submit
  *only* the turns its presented capability admits `submit` on. A turn for an
  agent the token does not authorize is refused by Row-Level Security — proven
  live (`write_path_rls_refuses_submitting_for_an_unauthorized_agent`, and on a
  standalone `psql` db). **Postgres never executes** — it records an intent the
  verifier must accept; writes stay verified-only, reads stay free SQL.

This is the load-bearing half: the *gate* (a pg role submits exactly what its
caps allow) and the *enqueue* are real and enforced by the engine. What remains
for **M3** is the **node-side drainer** that closes the loop:

1. **The drainer task** (node-side, `node/src/pg_mirror.rs` or a sibling
   `pg_submit_drainer.rs`): a tokio task that, when `DREGG_PG_MIRROR_URL` is set
   and the `pg-mirror-live` feature is on, `LISTEN`s / polls
   `SELECT * FROM dregg.submit_queue WHERE status='pending' ORDER BY submitted_at`
   as the `dregg_kernel` role (BYPASSRLS; it must read every pending row).
2. **Execute through the real verifier** — for each pending row, `postcard`-decode
   `signed_turn` into a `SignedTurn`, run the SAME gates the node's
   `POST /turns/submit` handler runs (signature, agent-derivation, receipt-chain),
   then `crate::executor_setup::execute_via_producer(&executor, &signed.turn,
   &mut ledger, lean_producer_enabled)` — the ONE executor gate (#171), which
   routes through the verified Lean producer. This is "the real executor +
   proof"; the spine holds because the *node*, not pg, executes.
3. **Resolve the row + mirror back** — on `TurnResult::Committed { receipt, .. }`,
   `UPDATE dregg.submit_queue SET status='executed', receipt_hash=…, resolved_at=now()`
   and let the existing commit-path mirror (`mirror_committed_record`) project the
   resulting `CommitRecord` into the `dregg.*` tables (or, under the Tier-C gate,
   submit the post-image batch through `dregg.commit_log`). On rejection,
   `status='refused', error=…`. Either way the same transaction boundary the
   commit log already guarantees applies.
4. **Backpressure + idempotency** — drain in submitted_at order, one turn per
   agent in flight (the agent nonce orders them), and make re-drain idempotent
   (a row already `executed` is skipped); a node restart resumes from the
   `pending` rows, losing nothing.

The drainer is bounded, ordinary node work (no new trust, no Lean-in-pg); it is
M3 because it touches the node's executor wiring and wants the live-pg connection
the M2 `PgSink` already establishes. The **proof**-soundness gate (the whole-chain
IVC light client attesting a receipt range) is the *other*, orthogonal M3 item —
see §10.2: it is what `dregg_verify_turn` honestly does NOT do per-row. Tier D
(§11.1–3) then collapses the drainer's out-of-process executor into the backend
for single-transaction atomicity — the north star, gated on the pg/Lean spike.

## 12. Integration wins (each composes with the spine)

- **Universal memory → ONE table (the elegance).** `docs/UNIVERSAL-MEMORY.md`
  proves dregg's whole state is one Blum multiset over `Domain × κ`, `Domain ∈
  {registers, heap, caps, nullifiers, index}`, with the four map roots as
  *derived boundary views*. That maps **exactly** onto one postgres table
  `dregg.memory(domain, collection, key, value, last_ordinal)` — a future state
  component is a new `domain` *value*, never a new table. The typed tables of
  §9 (cells/caps) can then be **views over this one relation**, and the boundary
  roots are `dregg_domain_root('caps', …)` aggregates whose equality with the
  committed map root is the Lean-proved `boundary_root_derived`. The single
  table *is* the honest model; the typed tables are query sugar. (ember decision:
  lead with typed tables for ergonomics, or with the single table for honesty?)
- **dregg-analyzer → pg as the trace/attestation store.** `dregg-analyzer`'s
  captures (blocklace / receipts / WAL / network / forest) and `AnalysisReport`s
  land in pg tables; the analyzer's safety findings become SQL the operator
  queries, and the attestation traces are durable and joinable to `dregg.turns`.
- **dregg-query → attested read SRFs (already §7).** Surface `dregg-query`'s
  evaluator as set-returning functions; an answer carries its MMR non-omission
  opening, so a `SELECT dregg_receipts(since)` is a *provably complete* answer,
  not just a view. This is the read-side complement to Tier C's verified writes:
  reads are not only free, they can be *attested* free.
- **persist snapshots → ship/install via pg.** `persist/src/snapshot.rs`'s
  `{checkpoint ⊕ overlay}` with the `claimed_root` anti-substitution tooth is
  exactly a Tier-B/C bootstrap: a joiner `COPY`s a snapshot into the mirror and
  the root-chain check (§10.1 step 2) re-validates it — node bootstrap as a SQL
  bulk-load.
- **The SDKs → a pg-backed dev loop.** With Tier D (or D-sidecar), the SDK's
  dev loop is `psql`: mint, submit turns, and query state without standing up a
  node — the lowest-friction "hello, dregg" a developer can have. This is the
  usability/teaching win the refinement epoch is asking for.

## 13. Recommended sequencing + feasibility verdicts

| Milestone | Tier | Deliverable | Verdict |
|---|---|---|---|
| **M1** (landed) | A | caps as RLS (`dregg_cap_admits`) | shipped |
| **M2** (landed) | B1 | the **mirror**: node tails its commit log into RLS-gated pg tables; the explorer + analytics as plain SQL — LIVE on pg18 (`cargo pgrx test pg18`; `node/src/pg_mirror.rs` `pg_live::PgSink` writes through over `tokio-postgres`) | **GREEN** |
| **M2.5** (landed) | C (chain tooth) | the **verified-store gate**: `dregg.commit_log` is the ONE door, its trigger runs the REAL chain re-validator `dregg_verify_turn` (the anti-substitution tooth, `mirror::verify_chain_step`) + materializes via the pg18 MERGE (`RETURNING old/new` reports the balance delta) — a tampered/reordered batch is refused by the engine. The write-path **outbox** (`dregg.submit_turn` + `submit_gate` RLS) lets a pg-user submit a verified turn FROM pg, gated to the agents its caps authorize | **GREEN** |
| **M3** (next) | C (proof) + outbox drainer | the **node drainer** that turns the §11 outbox real (queue → `execute_via_producer` → mirror); and the per-turn *proof* gate where the whole-chain IVC light client (`circuit::ivc_turn_chain`) attests the receipt range (the proof half `dregg_verify_turn` honestly does NOT do per-row, §10.2) | **GREEN/YELLOW** |
| **future** | B2 / D | promote the mirror to the node's persist backend (B2); the executor as a pg function (D) — front-loaded by the pg/Lean process-model spike — or D-sidecar | **YELLOW** (D, post-spike) |

> **Landed-state note (folded in).** M2 and the Tier-C chain tooth + the §11
> write outbox are **implemented and live on pg18**, not just designed. The
> `dregg_verify_turn` extension function is the REAL anti-substitution chain
> re-validator (the exact `mirror::verify_chain_step` gate `RootChain::extend`
> runs), proven through real SQL by `cargo pgrx test pg18` AND on a standalone
> live `psql` database. What remains for M3 is (a) the node-side **drainer** that
> executes queued turns through the real executor and (b) the orthogonal
> *proof*-soundness gate (the whole-chain IVC light client), which `dregg_verify_turn`
> deliberately does not attempt per-row because a `CommitRecord` carries no
> per-turn proof (§10.2). The chain tooth is the load-bearing, realizable per-row
> half of the spine invariant, and it is enforced by the database engine today.

The throughline is the spine: **M2 gives postgres a first-class query surface
with airtight soundness (only the node writes, apps read), M3 makes the verifier
the gate so even the writer cannot forge, and D is the endgame where postgres
becomes the node.** Each step is sound because each honours the one invariant —
no state row exists except as a verified-turn post-image — and the design's job
is to keep that invariant visibly load-bearing at every tier, never to trade it
for convenience.

### ember decisions surfaced (Part II)

5. **M2 = the B1 mirror** (node tails commit log → pg), or jump to B2 (pg as the
   node's persist backend)? Recommendation: B1 first (airtight, reversible);
   B2 once the schema is proven.
6. **Tier B tables: typed (cells/caps/turns) or the single universal-memory
   table** with typed views over it? Recommendation: typed tables for query
   ergonomics, documented as views over the one honest `dregg.memory` relation.
7. **Tier C verifier embedding: C-embed (verifier in the backend behind a
   `tier-c` feature — authorized, §8.1) vs C-callout (a co-located node
   verifies)?** Recommendation: C-embed is the first-class path; C-callout only
   if the carve-out is too Lean-entangled.
8. **Tier D: pursue the in-backend Lean executor (authorized, §8.1), or stop at
   D-sidecar** (SQL submit ergonomics, node executes over a socket, no Lean in
   the backend)? Recommendation: run the pg/Lean process-model **spike** first;
   if clean, pursue full D for the single-transaction atomicity payoff;
   otherwise D-sidecar is 75% of the payoff at a fraction of the risk.

> **Note (correction folded in).** An earlier draft treated `pg-dregg`'s
> circuit-free / offline profile as a design boundary for the whole crate and so
> ranked C/D as heavyweights to avoid. That was wrong: the offline profile is a
> property of **Tier A only**; `pg-dregg` is authorized to link circuits and
> operate online for the tiers that need it (§8.1). The verdicts above reflect
> the corrected stance — C and D are first-class, authorized targets, gated only
> by their genuine engineering (the verifier carve-out; the pg/Lean process
> model), not by any prohibition on linking the proof stack.

### 13.1 The four open ember-decisions — recommended, with reasons

The decisions surfaced in §6 (1–4) and §13 (5–8) collapse to four that actually
gate work. Each below is the *recommended* call, with the reasoning a decider
needs and the implementation consequence — so the choice is "confirm or override",
not "rediscover the tradeoff".

1. **Default revocation = instant, NOT bounded-staleness (override the §6/§3.4
   default).** The doc's *original* framing made bounded-staleness-via-TTL the
   default and instant the opt-in. The code already went the other way and it is
   right: `authz::decide` consults the revocation registry on **every** call
   (including hot-LRU hits — only the ed25519 chain verify is cached, never the
   verdict), so a revoked credential's rows vanish on the **very next statement**
   (`instant_revocation_makes_rows_vanish`, live pg18). TTL is still the
   *clustered-horizon* fallback (a backend that has not yet seen a `dregg.revoked`
   row), but the single-node default is instant, at no extra infrastructure.
   *Consequence:* `dregg_cap_not_revoked` ships M1 (it does), and the per-row cost
   of the registry check is a hash-set lookup — negligible beside the cached
   chain. **Confirm: instant is the default.**

2. **Tier-B tables = TYPED (cells/caps/turns), documented as views over the one
   `dregg.memory` relation (decision 6).** Lead with the typed tables for query
   ergonomics — `SELECT balance FROM dregg.cells` is the "your node IS your
   postgres" story; `SELECT value FROM dregg.memory WHERE domain='registers'` is
   the honest model but a worse hello-dregg. The single `dregg.memory` multiset
   (one row per `(domain, collection, key)`, the §12 universal-memory collapse)
   IS shipped and IS the honest substrate; the typed tables are its query sugar.
   *Consequence (the one real follow-up):* today the typed tables and `dregg.memory`
   are populated **in parallel** by the writer rather than the typed tables being
   literal `VIEW`s over `dregg.memory` — promoting them to views (so a new state
   component is provably just a new `domain` value) is a clean, additive M-future
   refactor, not a v1 blocker. **Confirm: typed-tables-lead; views-over-memory is
   the documented end state.**

3. **Tier-C verifier = C-EMBED, behind the `tier-c` feature (decision 7).**
   Embedding the Lean-free circuit verifier (`dregg-circuit --features
   verifier`/`recursion`) is the *point* of the verified store (§8.1), not a
   reluctant heavyweight — the database itself attests every proof. The whole-chain
   IVC light client already isolates the verifier from the executor, so the
   carve-out is bounded (the §10.2.1 settle items S1/S3). C-callout (a co-located
   node verifies over RPC) is the **fallback only** if the carve-out proves more
   Lean-entangled than the light-client framing suggests — it preserves soundness
   but adds a synchronous dependency + a trust boundary. *Consequence:* the
   range-attest SRF shape ships now (fail-closed stub); flipping `tier-c` on is
   S1/S3. **Confirm: C-embed; C-callout is the documented fallback.**

4. **Tier-D = run the pg/Lean process-model SPIKE first; full-D if clean, else
   D-sidecar (decision 8).** Tier D (the verified Lean executor *in* the backend,
   so a turn and the app's own rows commit in ONE transaction) is the most-sound
   tier — the kernel itself is the writer — and the unique payoff (cross-domain
   atomicity no separate node can offer). The single real hazard is technical, not
   policy: pg's `setjmp`/`longjmp` error unwinding vs a Lean runtime mid-stack
   (§11.3). So the call is **conditional**: front-load a small spike that links
   the executor into one backend and hammers the error path; if clean, pursue full
   D; if not, **D-sidecar** (`dregg_submit_turn` hands the envelope to a co-located
   node over a unix socket — SQL submit ergonomics, no Lean in the backend, ~75%
   of the payoff minus the single-transaction atomicity) is the sound stepping
   stone. *Consequence:* neither blocks M3 — the §11.4 outbox + drainer is the
   realizable write path; D is the post-M3 north star. **Confirm: spike-gated full
   D; D-sidecar as the de-risked alternative.**

# Part III — PostgreSQL leverage

`pg-dregg` targets **PostgreSQL 18** as its primary backend (the current
release, 2025-09). The extension builds and its full test suite runs against a
brew `postgresql@18` via `cargo pgrx test pg18`; pg13–pg17 remain selectable for
older deployments. The **pg18-specific leverage** — virtual generated columns,
`MERGE … RETURNING old/new`, `uuidv7()`, the `oauth` auth method, and
asynchronous I/O — has its own first-principles writeup in
**`docs/PG-DREGG-PG18.md`**. This part is the broader survey: the pg15–18
features that matter to the dregg mirror, which are **applied** (shipped +
test-proven) versus **designed** (a clear milestone), and the
federation-via-replication path. (Feature provenance below is attributed to the
release that introduced each feature — e.g. `JSON_TABLE` is pg17 — and all of
them are present in the pg18 primary target.)

## 14. The feature survey — what pg15–18 bring the mirror

### 14.1 Applied — shipped in the schema and proven by a test

> The four pg18-specific items below are detailed from first principles in
> `docs/PG-DREGG-PG18.md`; they are summarized here so the survey is complete.

- **Virtual generated columns (pg18)** — `pg18` makes `VIRTUAL` (read-time, zero
  storage) the default kind for generated columns. `dregg.cells` chooses the kind
  per column by whether it must be indexed: `cell_hex` is `STORED` (it backs the
  `cells_by_canonical` index — a virtual column cannot be indexed), while
  `cell_root_hex` / `balance_field` are `VIRTUAL` (read-side projections that need
  no index, so the write path materializes only what is indexed). Drift-free
  either way. *Proven by* `pg18_merge_returning_delta_virtual_columns_and_uuidv7`
  (the virtual columns equal their source on read; `pg_attribute.attgenerated` is
  `v`/`s` as designed) — `docs/PG-DREGG-PG18.md` §4.
- **`MERGE … RETURNING old/new` (pg18)** — `pg18` adds `old.*` / `new.*` to
  `RETURNING` for INSERT/UPDATE/DELETE/MERGE, so the `dregg.merge_cell` applicator
  reads the *pre-image* in the same atomic statement and reports the exact state
  delta (`'INSERT +1000000'` / `'UPDATE -500'`) — an audit signal impossible
  pre-18 without a separate pre-read. *Proven by*
  `pg18_merge_returning_delta_virtual_columns_and_uuidv7` (the INSERT and UPDATE
  arms return the signed delta) + the live `sql/e2e-live.sql` step 4b —
  `docs/PG-DREGG-PG18.md` §7.
- **`uuidv7()` (pg18)** — the `dregg.submit_queue` primary key defaults to the
  pg18 temporally-sortable `uuidv7()`, so the node drains the write outbox in
  arrival order by `id` alone and the index is append-friendly (no random-uuid v4
  page churn). *Proven by* the same test (the queue default mints a version-7
  uuid) — `docs/PG-DREGG-PG18.md` §6.
- **OAuth (`oauth` auth method, pg18) — composed, not bespoke.** pg18's `oauth`
  `pg_hba` method authenticates a connection against an external IdP and maps it
  to a pg role; the §6 login event trigger then turns that role into its dregg
  capability (`dregg.role_identity` → the `dregg.token`/`dregg.agent` GUCs), so an
  OAuth subject's authority inside the database IS its dregg capability, gated by
  RLS on every row. (Deployment configuration, not extension SQL — see
  `docs/PG-DREGG-PG18.md` §6.)
- **Asynchronous I/O (pg18) — applied + observable.** The read-heavy mirror's
  large scans (`dregg.cells`, `receipt_chain`, the recursive `cap_edges` walk) ride
  pg18's AIO with no SQL change. The AIO observability surface is **wired**:
  `dregg.mirror_io_stats` projects the read-path-relevant `pg_stat_io` relation
  contexts (with the pg18 `reads`/`read_bytes`/`hits` columns) into a compact
  view reporting the per-context read/write counts and the `cache_hit_ratio` the
  mirror watches as the ledger grows. *Proven by* `pg18_mirror_io_stats_view_reports_the_io_mix`
  (live pg18) — `docs/PG-DREGG-PG18.md` §8.
- **B-tree skip scan (pg18) — applied.** The composite `cells_by_mode_balance
  (mode, balance)` index serves both `WHERE mode = …` and `WHERE balance = …` /
  `ORDER BY balance` — the latter via skip scan over the tiny-cardinality leading
  `mode` column, so one index covers two hot read paths with no separate balance
  index on the write path. *Proven by*
  `pg18_skip_scan_serves_balance_with_unconstrained_leading_mode` (live pg18) —
  `docs/PG-DREGG-PG18.md` §8.
- **`security_invoker` views (pg15) — applied.** Every dev-view is created `WITH
  (security_invoker = true)`, so the base-table RLS is evaluated as the invoking
  reader THROUGH the view — the capability gate is enforced by declaration, not
  incidentally. *Proven by* `pg15_security_invoker_views_enforce_rls_through_the_view`
  (live pg18) — `docs/PG-DREGG-PG18.md` §6/§8. (This is the §14.3 hardening, now
  wired rather than noted.)
- **`uuid_extract_timestamp` / `_version` (pg18) — applied.** The
  `dregg.submit_queue_audit` view recovers the enqueue time + version FROM the
  `uuidv7()` key (so the key is itself an audit signal, cross-checking the
  `submitted_at` clock). *Proven by* `pg18_submit_queue_audit_recovers_time_from_the_uuidv7_key`
  (live pg18) — `docs/PG-DREGG-PG18.md` §6.
- **`RETURNING WITH (OLD/NEW)` typed applicator (pg18) — applied.** Beyond the
  string `'<ACTION> <DELTA>'` form, `dregg.merge_cell_delta` returns the typed
  `(action, balance_delta, nonce_delta)` tuple (both read off the pre-image), so
  conservation is assertable directly off the applicator. *Proven by*
  `pg18_merge_cell_delta_typed_and_conservation_off_the_applicator` (live pg18) —
  `docs/PG-DREGG-PG18.md` §7.

- **SQL/JSON `JSON_TABLE` (pg17)** — the embedded jsonb state, projected into a
  flat relational surface. dregg's cells carry decoded field slots
  (`cells.fields_json`) and capabilities carry their attenuation
  (`capabilities.allowed_effects`) as jsonb; `JSON_TABLE` turns those into proper
  rows a developer JOINs and aggregates without hand-rolled jsonb operators. Two
  dev-views ship:
  - `dregg.cell_fields` — `balance`/`nonce` projected out of `fields_json` as
    typed columns (`JSON_TABLE(fields_json, '$' COLUMNS(balance bigint PATH
    '$.balance', …))`).
  - `dregg.cap_attenuations` — one row per effect in a capability's
    `allowed_effects` array (`JSON_TABLE(allowed_effects, '$[*]' COLUMNS(effect
    text PATH '$'))`); this is the **no-amplification audit surface** exploded
    into rows (a child's allowed effects ⊆ its grantor's, queryable directly).

  *Why it matters:* the mirror's value is "your node IS your postgres" — the
  richer the relational query surface over dregg's embedded JSON, the more of the
  explorer/analytics story is plain SQL. *Proven by* `pg17_merge_upsert_and_json_table_views`
  (`src/lib.rs`, run under `cargo pgrx test pg18`) + `ddl_is_emittable_…` /
  `emitted_ddl_agrees_with_committed_sql_file` (`src/mirror.rs`, `cargo test`).

- **`MERGE` + `merge_action()` RETURNING (pg17)** — the node→pg row
  materialization as one atomic statement. The mirror writer upserts each touched
  cell's post-image with a single `MERGE` (a first-seen cell INSERTs, a re-touched
  cell UPDATEs in place), and pg17's `merge_action()` RETURNS which arm fired so
  the write is auditable. It ships as the `dregg.merge_cell(...)` function (the
  same one the `mirror::ddl` emitter generates and `schema-tierB.sql` mirrors); the
  Tier-C trigger materializes the post-state the same way (`schema-tierC.sql §3`).

  *Why it matters:* `MERGE` replaces the older `INSERT … ON CONFLICT` upsert with
  the standard atomic form and gives a first-class audit signal (`merge_action()`),
  and it is the natural shape for "materialize the verified receipt's touched
  cells." *Proven by* `pg17_merge_upsert_and_json_table_views`: across the
  synthetic story ALICE is INSERTed at ord 1 then UPDATEd at ord 2/3, and the test
  asserts exactly one ALICE row with the latest post-image's nonce (the update arm
  won, no duplicate insert).

  > **pgrx-0.17 note (named seam, not a pg17 gap).** A top-level `MERGE` issued
  > through pgrx's `Spi` panics with *"unrecognized SPI status code: 19"* —
  > `SPI_OK_MERGE` (19, added in PG15) is outside the `1..=18` range pgrx-0.17's
  > Spi wrapper maps. The fix is clean and is the better design anyway: the
  > `MERGE` lives inside the `dregg.merge_cell` SQL function (where the MERGE
  > status is consumed by the function executor), invoked as a plain
  > `SELECT dregg.merge_cell(…)`. So the mirror gets a real pg17 MERGE *and* a
  > server-side, reusable materialization function. (A future pgrx that maps
  > status 19 would also let a top-level MERGE run; we do not depend on it.)

- **`COPY … ON_ERROR` + `LOG_VERBOSITY` (pg17)** — robust bulk ingest for mirror
  backfill. A subscriber/replica that backfills the mirror from a dump of
  verified-turn post-images should not abort the whole load on one malformed row;
  `ON_ERROR ignore` skips and reports them. *Applied as the documented batch-ingest
  form* in `schema-tierC.sql §4b`. This is **ingest robustness only** — the
  per-turn verifier trigger still gates every row that lands, and the chain tooth
  refuses the resulting ordinal gap, so a partial backfill fails *closed* (a
  skipped row is absent, never an unverified write).

### 14.2 Designed — a clear milestone (see §15 for the big one)

- **Logical replication: failover slots + `pg_createsubscriber` (pg17)** — the
  **distributed-mirror / federation-via-pg** path. Designed in §15.
- **Incremental backup (`pg_basebackup --incremental` + `pg_combinebackup`,
  pg17)** — the snapshot/checkpoint complement: `persist/src/snapshot.rs`'s
  `{checkpoint ⊕ overlay}` with the `claimed_root` anti-substitution tooth maps
  onto pg17 incremental backups. A full base backup is the checkpoint; nightly
  incrementals are the overlay; `pg_combinebackup` reconstructs a point-in-time
  mirror whose `dregg.turns` head root is then re-validated by the chain tooth
  (§10.1 step 2) — so a restored mirror is *self-checking*, not merely restored.
  *Milestone B-snapshot:* wire the mirror's bootstrap to consume pg17 incrementals
  and re-validate the head root on restore.
- **`pg_stat_io` (pg16/18 AIO) — the observability VIEW is applied (§14.1); the
  perf BASELINE remains the milestone.** `dregg.mirror_io_stats` (over the pg18 AIO
  `pg_stat_io`) makes the read/write/verify I/O mix legible per (backend, context)
  with the cache hit ratio. What remains designed is the *quantified baseline*:
  running the dev-views under load and documenting the read amplification of the
  RLS predicate (the numbers, not the surface — the surface ships).

### 14.3 RLS / extension-API notes (pg15–17)

- **`SECURITY_INVOKER` views (pg15) — WIRED.** Every dregg dev-view (`cap_edges`,
  `cell_balances`, `receipt_chain`, `cap_attenuations`, `cell_fields`,
  `canonical_cells`, and the new `mirror_io_stats` / `submit_queue_audit` /
  `role_bindings`) is now created `WITH (security_invoker = true)`, so the
  base-table RLS is evaluated as the *invoking reader* THROUGH the view — the
  capability gate is enforced by declaration, so a future owner-privileged
  base-table change cannot silently widen a view. (Was "cheap hardening, noted";
  now applied — see §14.1 and `pg15_security_invoker_views_enforce_rls_through_the_view`.)
- **`MAINTAIN` privilege + non-superuser `REFRESH MATERIALIZED VIEW` (pg16)** —
  if the mirror ever promotes a hot dev-view to a materialized view, pg16 lets a
  non-superuser maintenance role refresh it, keeping the write-lockdown role model
  (the kernel writes state; a separate low-privilege role maintains derived views)
  without granting ownership. *Noted for the materialized-view path.*
- **RLS is already the spine's read gate** — pg-dregg's read-side security is the
  M1 cap layer expressed as RLS policies (`dregg_admits`), `FORCE ROW LEVEL
  SECURITY` on every state table, and the `dregg_reader`/`dregg_kernel` split.
  pg15–17 bring no RLS *semantics* change that weakens or requires reworking this;
  the `SECURITY_INVOKER` view note above is the one cheap strengthening.

## 15. The distributed-mirror milestone — federation via logical replication

**The target (Tier-B-distributed):** a *subscriber* postgres node tails a
*publisher's* dregg mirror, so dregg state propagates between pg nodes by
PostgreSQL's own logical replication — federation-via-pg, no bespoke gossip. This
is the pg-native expression of the dregg federation story (strand = feed,
blocklace = DAG): the publisher's `dregg.turns` hash chain is the replicated feed,
and a subscriber that tails it is a read replica of verified dregg state.

**The publication/subscription shape.**

```
-- on the publisher (the authoritative dregg mirror node):
CREATE PUBLICATION dregg_mirror
  FOR TABLE dregg.turns, dregg.cells, dregg.capabilities, dregg.memory;

-- stand up the subscriber from a consistent base with pg17 pg_createsubscriber
-- (converts a physical standby into a logical subscriber WITHOUT a fresh dump —
-- the subscriber starts already caught up to a consistent point):
pg_createsubscriber -d dregg -P "host=publisher ..." --publication=dregg_mirror

-- the subscription tails the publisher's verified-turn stream thereafter:
CREATE SUBSCRIPTION dregg_tail
  CONNECTION 'host=publisher dbname=dregg'
  PUBLICATION dregg_mirror
  WITH (failover = true);     -- pg17 failover slots: survive publisher failover
```

**Why pg17 specifically.**

- **`pg_createsubscriber` (pg17)** turns a physical standby into a logical
  subscriber *without* a fresh logical dump/restore — so a subscriber bootstraps
  from a consistent snapshot of the whole mirror (a real ledger can be large) and
  then tails. Pre-17 this meant a full re-copy; pg17 makes joining cheap.
- **Failover slots (`failover = true`, pg17)** make the subscription survive a
  publisher failover: the replication slot is synchronized to the publisher's
  standbys, so when the publisher fails over the subscriber keeps tailing the new
  primary without losing its place. For a federation where the authoritative
  mirror itself is HA, this is what keeps the tail unbroken.

**Does the RootChain tooth survive replication? Yes — and it is what makes a
replicated mirror trustworthy rather than merely fast.** The anti-substitution
tooth (`src/mirror.rs::RootChain`) is *structural*, defined purely on the
`turns` rows: turn *N*'s `ledger_root` must equal turn *N+1*'s `prev_root`, and
ordinals are dense. Logical replication copies the `turns` rows verbatim, so the
chain is preserved bit-for-bit across the wire — the subscriber can re-run
`RootChain` over its replicated `dregg.turns` and get the identical accept/refuse
verdict the publisher did. Three consequences:

1. **A subscriber re-validates, it does not trust.** On apply (or as a periodic
   sweep), the subscriber walks its replicated `dregg.turns` through the same
   `RootChain::extend` and refuses a head that does not chain. A corrupted or
   tampered replication stream that reordered/substituted a turn is caught by the
   tooth on the subscriber side — replication is *not* a trust boundary the tooth
   has to assume away.
2. **The hash chain is the replication invariant.** Because `prev_root`/`ledger_root`
   travel *in the rows*, "the subscriber's mirror chains" is checkable locally,
   with no call back to the publisher — exactly the light-client property §10.1
   gives a single node, now extended to a replica.
3. **Tier C composes.** If the subscriber also runs the Tier-C verifier
   (`tier-c` feature), it can re-verify each replicated turn's proof against the
   replicated receipt, not just the chain — a subscriber that is a *full* verifier
   of the publisher's stream. The chain tooth is the cheap structural half every
   replica enforces; the verifier is the expensive complete half a verifying
   replica adds.

**Honest scope.** The *soundness-load-bearing* piece is **built**; the
*replication wiring* is operational config (a publisher conninfo + a
`pg_createsubscriber` run), which the extension cannot perform on a DBA's behalf.
Built and `cargo test`-proven (`pg-dregg/src/mirror.rs`): (a) the
**`federation_publication()` DDL emitter** (`CREATE PUBLICATION dregg_mirror` over
the four state tables + `turns`) and its `dregg_install_federation()` extern; (b)
**`revalidate_replicated_chain()`** — the subscriber-side sweep that walks the
replicated `dregg.turns` through the SAME `verify_chain_step` tooth the publisher
ran, surfaced as the `dregg_revalidate_replicated_chain()` extern; it returns the
re-validated head, or **refuses** a substituted / reordered / gapped / truncated
stream — caught *on the subscriber side, locally, with no call back to the
publisher* (`subscriber_catches_a_substituted_replicated_turn`,
`subscriber_revalidates_the_synthetic_story_after_replication`); and
**`federation_health()`** — the composition that makes the pg18 apply-conflict
alarm DRIVE that re-validation: it reads the real `dregg.replication_conflicts`
`confl_*` counters and, when `conflicts_total > 0` (an apply-level divergence pg
detected), TRIGGERS `revalidate_replicated_chain`, returning a verdict that
escalates `Clear → ConflictsButChainIntact → ConflictsAndChainBroken`. The two
checks compose on two layers — the counters catch an apply divergence, the tooth
catches a substituted root — and a non-zero conflict count is exactly the trigger
to re-run the tooth (surfaced as the `dregg_federation_health()` extern; the
postgres-free composition tests in `src/mirror.rs`, the live
`federation_health_conflict_alarm_triggers_the_chain_tooth`, and the
genuine-counter harness `scripts/federation-conflict-live.sh`). Operational
(emitted as a runbook, `federation_subscriber()` / the
`dregg_federation_subscriber_runbook(conninfo)` extern): (c) the
`pg_createsubscriber` bootstrap + the `CREATE SUBSCRIPTION … WITH (failover =
true)`. Optional: (d) the Tier-C verify-on-tail (`dregg_attest_range` on the
replicated stream) for a *full verifying* replica. The load-bearing claim — *the
RootChain tooth survives replication and lets a subscriber re-validate locally* —
is exactly what `revalidate_replicated_chain` enforces, because the tooth is
defined on the replicated rows themselves.

### 15.1 Tier-B-distributed verdict: **GREEN — the re-validation is built; replication is config**

The chain tooth being structural-on-the-rows is what makes this sound: a
replicated mirror is a re-validating replica, not a trusted copy. pg17's
`pg_createsubscriber` + failover slots remove the two operational blockers
(expensive join, fragile slot across failover). The **soundness piece is now
built** — the publication emitter + the subscriber re-validation sweep
(`revalidate_replicated_chain`, `cargo test`-proven; the
`dregg_install_federation` / `dregg_revalidate_replicated_chain` externs) — so a
subscriber re-validates the replicated chain locally and refuses a tampered
stream. What remains is the per-deployment *replication config* (the publisher
conninfo + the `pg_createsubscriber` bootstrap), which the
`dregg_federation_subscriber_runbook` extern emits but only a DBA can run. The
verifying-replica option (Tier-C `dregg_attest_range` on the tail) composes on
top once the §10.2.1 circuit-link lands.
