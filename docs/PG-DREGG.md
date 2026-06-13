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
-- Issue a credential carrying caveats encoded as a small JSON DSL
-- (mirrors the Pred algebra: {"attr_eq":{"key":"tool","value":"read"}}, etc).
-- The issuer private key is read from a SUPERUSER-only GUC; this function is
-- itself SECURITY DEFINER and only callable by the app's issuing role.
CREATE FUNCTION dregg_mint(subject text, caveats jsonb, until bigint) RETURNS text;

-- Attenuate a presented token by appending caveats — never widening.
CREATE FUNCTION dregg_attenuate(token text, caveats jsonb) RETURNS text
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
- **caveats JSON** (mint/attenuate only) — SQL `jsonb` ⇄ a small serde DSL
  mapping 1:1 onto the `Pred` enum (`{"not_after":2000}`,
  `{"attr_prefix":{"key":"resource","value":"org/42/"}}`,
  `{"all_of":[…]}`). The DSL is the `Pred` algebra; nothing new is invented.

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

**Pinning.** `pgrx = "0.17"` (latest; supports `pg13`–`pg18` via the
`pg13`…`pg18` features). Target **pg16** for milestone 1 (the common modern
default; widely deployed, fully RLS-capable). `dregg-auth` is a path dependency
(`{ path = "../dregg-auth" }`), default features — it is already circuit-free,
so no feature surgery is needed.

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
cargo pgrx init --pg16 <download|path-to-existing>
cargo pgrx test pg16        # runs the #[pg_test]s against a managed pg16
cargo pgrx run  pg16        # opens psql with the extension loaded
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
