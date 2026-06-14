# pg-dregg vs DBOS — durable execution, and what a *verified turn* adds

DBOS gives an application **durable execution** on PostgreSQL: a workflow's inputs
and each step's output are checkpointed to postgres, and after a crash the
workflow resumes from its last completed step — exactly-once, no separate
orchestrator, nothing but postgres. That is real and valuable.

`pg-dregg` gives durable execution **where every state mutation is a verified,
capability-secure, conservation-respecting turn.** The durability is the same
shape — a crash-safe log you replay — but the *thing being logged* is different:
not an opaque step output a trusted writer produced, but a **verified turn** whose
post-state the database engine itself re-validates before it can become a row.

This document states, from first principles and in present tense, what
`pg-dregg` does that DBOS does not, and is honest about what is shipped today
versus what is on the frontier. It does not narrate a trajectory; it describes
what is.

---

## 1. The one-sentence difference

> DBOS makes your workflow **durable**. `pg-dregg` makes your workflow durable
> **and** makes every state change **unforgeable, attenuable, conserving, and
> federated** — because state mutates only through a verified turn, never through
> a bare `UPDATE`.

DBOS trusts the writer: a step is ordinary code that issues an ordinary
`UPDATE`, and DBOS's job is to make sure that code runs exactly once. `pg-dregg`
does not trust the writer: a row representing protocol state exists **only** as
the post-image of a verified turn, and the database engine refuses anything else
(`docs/PG-DREGG.md` §8, the spine invariant).

---

## 2. What DBOS is (so the comparison is fair)

DBOS-Transact is a library, not a server. It uses postgres to orchestrate
durable workflows:

- **Checkpointing.** When a workflow starts, its inputs are written to a
  system table; as each step completes, its output is written too.
- **Replay-from-last-step recovery.** On a crash/restart, DBOS reads the
  checkpoints and re-runs the workflow, skipping steps whose output is already
  recorded (it returns the recorded output instead of re-executing).
- **Exactly-once via idempotency.** Each workflow and step gets an idempotency
  key; external effects are made exactly-once as *at-least-once + idempotent*,
  and DB-only steps ride a single postgres transaction.

This is a genuinely good durability story, and `pg-dregg` does **not** claim to
beat DBOS *at durability*. The point is what `pg-dregg` adds *on top of* a
durability story of the same shape.

The shared substrate is the honest common ground: both are "postgres is the
system, no separate orchestrator." `pg-dregg`'s mirror is a crash-safe,
replayable log (`docs/PG-DREGG.md` §9–§11) for exactly the reasons DBOS uses
postgres — ACID, backups, PITR, replication — and a restarted `pg-dregg`
node/drainer resumes from the durable `dregg.turns` head (`RootChain::resume`)
just as a DBOS workflow resumes from its last checkpoint.

---

## 3. What `pg-dregg` does that DBOS cannot

Each row below is a property `pg-dregg` enforces and DBOS structurally cannot,
because DBOS's steps are arbitrary code over arbitrary `UPDATE`s.

| Property | DBOS | pg-dregg |
|---|---|---|
| **Durable execution** (crash → replay, exactly-once) | ✅ the core feature | ✅ the same shape (`RootChain::resume` from the durable `dregg.turns` head; a committed turn cannot be re-applied) |
| **Unforgeable writes** (a state row exists ONLY as a verified-turn post-image) | ❌ a step can issue any `UPDATE`; DBOS makes it run *once*, not *correctly* | ✅ the ONE door is `dregg.commit_log`, whose `BEFORE INSERT` trigger runs the real anti-substitution chain tooth (`dregg_verify_turn` / `verify_chain_step`); a forged/reordered/substituted batch is RAISEd by the engine |
| **Capability security** (an actor is bounded by an attenuable, offline-verifiable, sub-delegable token) | ❌ authorization is application code + postgres `GRANT`s (central DDL, no bearer credential) | ✅ each actor holds a dregg capability; `granted ⊆ held` is provable (`attenuate_subset`), RLS gates every row by it, and the write gate (`submit_gate`) admits only the turns a token authorizes |
| **No amplification** (a delegate provably holds strictly less than its grantor) | ❌ no notion of delegation narrowing | ✅ fuzzed: `attenuation_never_amplifies` over arbitrary caveat trees (`tests/proptest_authz.rs`) |
| **Value conservation** (Σδ = 0 across a turn) | ❌ a step can credit without debiting | ✅ a property of the executor's transition function; assertable directly off the pg18 `MERGE … RETURNING old/new` applicator (`docs/PG-DREGG-PG18.md` §7) |
| **Self-checking federation** (a subscriber re-validates the replicated stream, does not trust it) | ❌ logical replication, but a subscriber trusts the feed | ✅ the `RootChain` tooth survives replication (it is structural on the `turns` rows); a subscriber re-runs it locally, and a pg18 apply-conflict alarm DRIVES the re-validation (`dregg_federation_health`, `docs/PG-DREGG.md` §15) |
| **Reads are free SQL, provably sound** | ✅ reads are SQL (no special discipline) | ✅ reads are SQL *and* sound by construction (a `SELECT` cannot break a transition-function invariant), RLS-gated by the same capability |

### The money-printing bug, concretely

A DBOS step that contains the bug

```python
@DBOS.step()
def pay(ledger, who, amount):
    ledger.execute("UPDATE balances SET amount = amount + %s WHERE id = %s", (amount, who))
```

with a sign error, an SQL-injection, or a compromised caller, **executes** — and
DBOS faithfully makes it execute exactly once. Value is forged, durably.

The identical mutation in `pg-dregg` cannot enter the store:

- there is no `UPDATE` grant on `dregg.cells` (the Tier-B privilege lockdown:
  `REVOKE … FROM PUBLIC`, `FORCE ROW LEVEL SECURITY`);
- the only door is `dregg.commit_log`, and its trigger refuses a batch that does
  not carry a verified turn chaining onto the head root;
- and the turn's transition function conserves value, so a credit without a
  debit is not a representable turn.

The flagship demo (`pg-dregg/examples/supply_chain.rs`, §8) submits exactly this
forged write and shows the engine refuse it, head unmoved, balance unchanged.

---

## 4. The integrated story, runnable

`pg-dregg/examples/supply_chain.rs` is a four-party agentic supply chain (a
settlement bank, a buyer, a supplier, a shipper) fulfilling a purchase order as a
multi-step verified-durable workflow. It is the DBOS comparison made concrete:

- state lives in postgres; **reads are plain SQL** over the mirror; **writes are
  verified turns** through the submit path;
- each agent holds an **attenuated capability** and provably cannot act outside
  its grant (the buyer cannot mint a treasury balance or pay itself as the
  shipper);
- the workflow **survives a simulated crash** mid-flight and resumes
  **exactly-once** from the durable log (the chain refuses any re-apply of a
  committed turn);
- every step is a **receipted turn** (the turn's `creator` is the acting agent —
  provable who-did-what);
- **value is conserved** end-to-end (the order escrow nets to zero; Σ balances ==
  the genesis total);
- a **forged write is refused** by the spine;
- a **federation subscriber re-validates** the replicated chain and catches a
  tampered stream locally.

```text
cargo run --example supply_chain            # the postgres-free cores, end to end
cargo pgrx test pg18                         # the same surface through real pg18 SQL
pg-dregg/scripts/e2e-live.sh                 # the live write-path gate on a real db
```

---

## 5. The numbers

Measured over the postgres-free cores (`cargo bench`; the *algorithmic* cost of
the verification, isolated from pg/IPC — the honest "what does a verified turn
cost" number). Representative figures from this machine (Apple Silicon):

| path | what it is | latency | throughput |
|---|---|---|---|
| `submit_decision/hot_lru_reeval` | the verified-write gate (per row, LRU warm) | ~27 µs | ~37K admissions/s |
| `submit_decision/cold_full_chain_verify` | the verified-write gate (cold, full ed25519 chain verify) | ~75 µs | ~13K/s |
| `read_projection/rls_filter_rows` | the cap-gated RLS read (per row, hot) | ~26 µs/row | ~38K rows/s |
| `chain_gate/verify_chain_step` | the anti-substitution tooth (the Tier-C trigger gate) | ~3.5 ns | ~283M ops/s |
| `chain_gate/rootchain_extend` | the full chain-gate a MirrorBatch apply pays | ~4.3 ns | ~230M ops/s |
| `mirror_apply/from_parts_assemble` | assemble + well-formedness gate a verified turn | ~540 ns | ~1.85M/s |
| `mirror_serde/encode_batch` / `decode_batch` | the node↔pg wire codec per turn | ~2.9 µs / ~7.9 µs | ~920 / ~345 MiB/s |

End-to-end, the load generator (`cargo run --release --bin loadgen`) drives the
**full verified-write spine** (authz submit-gate + `RootChain` + apply) at
**~22K sustained verified turns/sec** on a single core, conserving value every
step. The per-turn cost is dominated by the capability decision (the ed25519
chain verify, amortized by the verified-credential LRU); the chain tooth itself
is effectively free (~3.5 ns).

The live-pg rate adds the SPI/IPC round-trip and the `MERGE` applicator on top of
these; it is exercised by `cargo pgrx test pg18` and `scripts/e2e-live.sh`.

---

## 6. Honest scope — shipped vs frontier

`pg-dregg` is a real, tested extension, and it is also honest about its tiers
(`docs/PG-DREGG.md` §8, the tier ladder). The comparison above is fair only with
this scope stated plainly:

**Shipped and tested (through `cargo test` + `cargo pgrx test pg18`):**

- **Tier A** — dregg capabilities as PostgreSQL RLS (the verified capability
  decision, attenuation, instant revocation, the issuer-key trust root). The
  authorization *semantics* are the machine-checked theorems of
  `metatheory/Dregg2/Authority/`, with the Lean↔Rust differential as the anchor
  (`docs/PG-DREGG.md` §4).
- **Tier B** — dregg state as RLS-gated, queryable postgres tables (the mirror:
  `dregg.cells/turns/capabilities/memory` + the JSON_TABLE / generated-column /
  skip-scan read surface). The node writes; apps read.
- **Tier C (chain tooth)** — the verified-store gate: `dregg.commit_log` is the
  ONE door, its trigger runs the **real** anti-substitution chain re-validator
  (`dregg_verify_turn`, the same `verify_chain_step` the in-process `RootChain`
  runs), and a tampered/reordered batch is refused by the database engine. The
  write-path **outbox** (`dregg.submit_queue` + the `submit_gate` RLS) lets a pg
  role submit a verified turn FROM postgres, gated to the agents its caps
  authorize.
- **Federation** — the publication emitter + the subscriber-side re-validation
  sweep (`revalidate_replicated_chain`) + the pg18 conflict-driven health check
  (`dregg_federation_health`). The subscriber re-validates; it does not trust.

**On the frontier (named, not claimed as done):**

- **Tier C (proof gate).** The per-row `dregg_verify_turn` is the *structural*
  chain tooth, not a per-turn STARK re-proof (a `CommitRecord` carries no
  per-turn proof; proof soundness is the whole-chain IVC light client's job,
  `docs/PG-DREGG.md` §10.2). The RANGE-attest SRF *shape* ships and is
  `cargo test`-proven, fail-closed; wiring it to the real circuit verifier is the
  named settle work (S1–S3 in `pg-dregg/src/attest.rs`).
- **Tier D — the executor in postgres (the north star).** `SELECT
  dregg_submit_turn(envelope)` *executing* the turn inside the backend (so a turn
  and the app's own rows commit in ONE transaction) is the AWESOME endgame and is
  **not done** — it is gated on the pg/Lean process-model spike (`docs/PG-DREGG.md`
  §11.3). The realizable write path today is the outbox + a node-side drainer (the
  node, not pg, executes); `D-sidecar` is the de-risked stepping stone.

So the honest claim is: **the verified-write *chain* discipline that makes
`pg-dregg`'s writes unforgeable is shipped and enforced by the database engine
today**; the **proof**-attestation and the **in-backend executor** are the named
frontier, with their realizable halves (the SRF shape, the outbox) already
landed. `pg-dregg` does not claim "the postgres layer is formally verified" — it
claims the *capability decision* and the *chain re-validation* are the verified
dregg checks, and it names the conventional integration seam (the GUC plumbing,
the trigger) explicitly (`docs/PG-DREGG.md` §4).

---

## 7. When to reach for which

- **Reach for DBOS** when you want durable, exactly-once workflow execution over
  application code you trust, with the least possible ceremony. It is excellent
  at that and `pg-dregg` does not replace it there.
- **Reach for `pg-dregg`** when the *writer cannot be fully trusted* — multiple
  parties / agents, value at stake, an audit requirement, a need to bound what a
  compromised or buggy step can do, or a federation where a subscriber must not
  trust the feed. `pg-dregg` gives you DBOS-shaped durability **plus** the
  guarantee that no state exists except as a verified, capability-bounded,
  value-conserving turn.

The two are not mutually exclusive: a DBOS-style durable workflow can submit its
state-changing steps as `pg-dregg` verified turns, getting durable orchestration
from one and unforgeable, attenuable, conserving state from the other.

---

Sources for the DBOS characterization: [DBOS Architecture](https://docs.dbos.dev/architecture),
[Why Postgres for Durable Execution (DBOS)](https://www.dbos.dev/blog/why-postgres-durable-execution),
[Durable Workflows in Postgres using DBOS (Supabase)](https://supabase.com/blog/durable-workflows-in-postgres-dbos).
