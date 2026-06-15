# PG-DREGG-ON-SEL4 — the deos spine: the persist-PD IS the "postgres" of the seL4 dregg OS

*Design + a runnable increment. Present-tense where the pieces are real (the
booting executor PD, the persist-PD seat in the assembly, the host witness that
runs the commit→read→chain-gate spine green); clearly-named where they are a
design or a wall (the in-qemu boot of the PD pair committing a turn over
`commit_out`; the redb-over-block-cap backend). First-principles, no trajectory
narrative. The safety argument is the spine — stated first, kept load-bearing.
Every seam is named as work with a closure lever, never a wall.*

**Companion docs.** This doc and `docs/PG-DREGG-ON-SEL4.md` answer two *different*
questions and are deliberately distinct:

- **`docs/PG-DREGG-ON-SEL4.md`** asks: *can we embed the literal 1.5-M-line
  Postgres C program into seL4 as a confined component?* Its answer is the
  VMM-guest ladder (a Linux-guest PD under libvmm, the in-process Tier-D executor,
  the native POSIX personality). That is "run **Postgres** in seL4."
- **THIS doc** asks the question `docs/PG-DREGG.md` actually distilled pg-dregg
  *to*: pg-dregg's model is **durable verified state** — *reads are free SQL,
  writes are verified turns, the store is durable*. The seL4 world already has the
  two organs that realize exactly that discipline — an **executor PD** (the
  verified writer) and a **persist PD** (the durable store). So "pg-dregg inside
  seL4" does **not** require porting Postgres at all: **the seL4 persist-PD IS the
  `dregg.turns` / commit-log of the seL4 deos foundation**, the executor-PD is its
  writer, and the discipline — not the C program — is what crosses. This doc builds
  that, with a green host witness.

Both are true and both are wanted; they are the *two surfaces* of "your node IS
your postgres" (`docs/PG-DREGG.md` §1): one keeps a real Postgres as a confined
query engine, the other realizes the same reads-free/writes-verified/durable
*spine* natively in the PD pair, no Postgres required.

---

## 0. The thesis, in one paragraph

pg-dregg's whole soundness is one invariant (`docs/PG-DREGG.md` §8): **postgres is
dregg's first-class store iff every state row appears only as the post-image of a
verified turn — reads are free `SELECT`, writes pass the verifier.** That invariant
is not about Postgres; it is about a *discipline* — a verified writer, a durable
append-only commit log, a chain gate that refuses any turn that does not chain onto
the prior, and free reads of the materialized state. The seL4 dregg OS already has
the two organs that discipline names: the **executor PD** runs the verified turn
(`dregg_exec_full_forest_auth`, boots today — `status:2 ok:1` inside a real seL4
protection domain, `docs/EMBEDDABLE-LEAN-RUNTIME.md` §4), and the **persist PD** is
the sole holder of the durable store (`sel4/dregg.system`, the `persist` seat). So
the seL4 deos foundation *is* pg-dregg's foundation realized in two PDs: the
executor commits a verified turn → the persist PD durably stores the committed turn
+ state (the `dregg.turns` analogue) → a read returns it (reads are free) → turn
*N+1* chains onto *N* (the Tier-C chain gate). This doc maps every pg-dregg concept
(the commit log, the submit queue, RLS-as-caps, the chain tooth) onto an seL4 PD
mechanism, and ships a **runnable host witness** (`sel4/persist-hosttest/`) that
drives the executor→persist→read spine + every anti-substitution tooth green —
reusing the **exact** pg-dregg chain-gate discipline (`mirror::verify_chain_step`),
not a reinvention.

---

## 1. The spine — the discipline, not the database

State it precisely, then map it.

> **THE DEOS SPINE.** The seL4 dregg OS is pg-dregg's "durable verified state"
> realized by a PD pair: the **executor PD** is the sole writer (it runs the
> verified turn and produces the post-state); the **persist PD** is the durable
> commit log + chain gate (it stores the committed turn and is the only door state
> enters); a **read is free** (any other PD / a light client queries the persist
> PD's materialized log without touching the writer). No state row exists in the
> durable store except as the post-image of a turn the executor verified and the
> persist PD's chain gate admitted. *Postgres is one possible face of this store
> (`docs/PG-DREGG-ON-SEL4.md`); the spine itself needs no Postgres.*

### 1.1 The mapping, concept by concept

The reason this is a *weld*, not a build (the WELD METHOD — the capability usually
already exists, disconnected): every pg-dregg concept has an seL4 organ already in
the tree. The table is the whole design in one view.

| pg-dregg concept | what it is (`docs/PG-DREGG.md`) | seL4 deos organ | where it lives today |
|---|---|---|---|
| **`dregg.turns` / the commit log** | one durable row per verified turn (`CommitRecord`: ordinal · turn_hash · creator · receipt_hash · ledger_root) | the **persist PD's durable commit log** | seat: `sel4/dregg-pd/persist-stub/`; logic: `sel4/persist-hosttest/src/commit_store.rs` (the missing organ, host-witnessed) |
| **the verified executor / the writer** | `execFullForestG` produces the only state rows; `dregg_submit_turn` never executes (§11.4) | the **executor PD** | `sel4/dregg-pd/executor-{pd,rootserver}/` — **boots** (`status:2 ok:1`, `docs/EMBEDDABLE-LEAN-RUNTIME.md` §4) |
| **the Tier-C chain gate** (`dregg.commit_log` trigger) | turn *N*'s `ledger_root` is turn *N+1*'s `prev_root`; a non-chaining turn is refused by the engine (`dregg_verify_turn` = `mirror::verify_chain_step`, §10) | the persist PD's **commit gate** — its sole door | `commit_store::verify_chain_step` (byte-identical to `pg-dregg/src/mirror.rs:477`) |
| **reads are free `SELECT`** | a `SELECT` cannot break a transition-fn invariant; it only observes (§8) | a **read of the persist PD's log** (by ordinal / turn_hash / receipt_hash) | `commit_store::lookup_by_*` (the redb index reads, §3) |
| **the submit queue / outbox** (`dregg.submit_queue` + `submit_gate` RLS, §11.4) | a confined component *enqueues* a signed turn; the drainer hands it to the one executor gate; the executor may refuse | the **ingress / net PD → executor `turn_in`** edge (an enqueue, not an execute) | seat: `sel4/dregg.system` `turn_in` (R into the executor); drainer logic: `node/src/submit_queue_drainer.rs` |
| **RLS-as-caps** (`dregg_admits`, the `dregg.token` GUC, §1–§6) | which rows a reader may read / which turns a role may submit, decided by the verified `dregg-auth` cap | the **seL4 cap partition** + the dregg cap *inside* it (n=1: an seL4 cap and a dregg cap are the same abstraction, `docs/FIRMAMENT.md`) | the assembly's c-space split; dregg-auth in the executor's admission |
| **the chain is self-checking** (a replica re-validates, §15.1) | a light client walks `dregg.turns` and re-checks `prev_root[N+1]==ledger_root[N]` | a **light-client walk of the persist PD's log** | `commit_store::iter_ordered` + the `chain_is_intact` walk (host witness `[4]`) |

The spine holds at the OS level for the same two reasons it holds in pg
(`docs/PG-DREGG.md` §8, §11.4):

- **the writer is the only writer.** Only the executor PD produces a `CommitRecord`;
  the persist PD's `commit_verified_turn` is the *only* mutator of the durable log,
  and it runs the chain gate first. No other PD holds a "write the ledger" cap — the
  seL4 cap partition enforces this *structurally* (the persist PD is the sole holder
  of the storage-device cap, `sel4/dregg-pd/persist-stub/src/main.rs`: "no other PD
  can ever touch the disk — the partition makes durable state unforgeable").
- **the gate refuses non-chaining state.** Even the executor cannot make the persist
  PD store a turn that does not chain onto the head: `verify_chain_step` is
  fail-closed (`ordinal == cursor` AND `prev_root == head`), so a stale, forged,
  out-of-order, or replayed turn is refused and the head does not move.

### 1.2 Why this is the honest "pg-dregg inside seL4"

The brief's correction is load-bearing: *running Postgres in seL4* (the giant C
codebase) is the `docs/PG-DREGG-ON-SEL4.md` VMM-ladder question, and it is real but
heavy. The **deos foundation** pg-dregg actually distilled is the *discipline*:
`docs/PG-DREGG.md`'s entire Part II is "postgres can be the store **iff** the spine
invariant holds," and Tiers B/C/D are increasingly-strong ways to *honour* it. The
seL4 PD pair honours it **natively** — the persist PD is the Tier-C verified store
(the chain tooth is its door), the executor PD is the Tier-D writer (the verified
kernel produces the rows). The "postgres" of the seL4 deos foundation is therefore
the **persist PD's commit log**, and the bridge from the live pg world is that the
persist PD runs *byte-for-byte the same chain-gate discipline* the live
`pg-dregg`/`persist` stack enforces — so the two stores are the same store with two
faces (a SQL face on a node; a redb-over-block-cap face on seL4).

---

## 2. The concrete increment — a green host witness for the persist-PD spine

The brief asks for "ONE verifiable step toward: the executor-PD commits a turn →
the persist-PD durably stores it → a read returns it," reusing the real pg-dregg
chain-gate discipline. That step is **built and green** as a host witness, exactly
in the shape `sel4/crypto-floor-hosttest/` established (host-test = the runnable
witness; the in-qemu PD-pair boot = the named macOS wall).

### 2.1 What exists, and the assessment of the persist seat

The persist PD's *seat* exists in the assembly (`sel4/dregg-pd/persist-stub/`): it
holds the durable-store place in the cap partition, maps `commit_out` (R), reads one
sentinel byte the executor seat wrote, and services the executor→persist
notification (channel id 1). **It holds the seat but stores nothing** — its own
doc-comment says so: "the real persist-PD is the durable store: commit log,
checkpoints, snapshot⊕overlay + root tooth … until [the block-cap backend] lands
this seat holds the persist place." So the *missing organ* is the persist PD's
durable verified commit log + chain gate. That organ is now written three ways that
share one gate: (a) the chain-gate discipline `no_std`+`alloc` over a `BTreeMap`
stand-in (`commit_store.rs`, rides INSIDE the persist PD via `#[path]`); (b) a
**REAL durable store** in `redb` ACID tables over a block-device `StorageBackend`
(`redb_store.rs`) — this makes "durable" *real* (a commit survives process death,
fsync at commit), not a map; and (c) the **app-hosting economy** on top
(`hosting.rs`) — pay-to-host as a conserving value turn, fee-lapse → eviction.

### 2.2 The files (the increment)

```
sel4/persist-hosttest/
  Cargo.toml              # standalone crate (empty [workspace]) — own target dir, swarm-safe;
                          #   deps: redb (the SAME ACID store persist/ uses) + tempfile (dev, the
                          #   real on-disk region the durability test reopens). Does NOT touch ./target.
  src/commit_store.rs     # THE GATE DISCIPLINE — the chain gate, no_std+alloc over a BTreeMap stand-in,
                          #   REUSING the pg-dregg discipline verbatim (rides INSIDE the persist PD):
                          #     - verify_chain_step  == pg-dregg/src/mirror.rs:477 (the anti-subst tooth)
                          #     - ChainRefusal        == pg-dregg/src/mirror.rs:356 (fail-closed)
                          #     - CommitRecord        == persist/src/commit_log.rs:82 (+ explicit prev_root,
                          #                              as pg-dregg's TurnRow carries, so the chain is
                          #                              checkable on the rows alone)
                          #     - commit_verified_turn== the commit_finalized_turn_with_burns ONE-TXN
                          #                              discipline (torn-state guard · idempotent replay ·
                          #                              append-then-index-then-cursor-LAST)
  src/redb_store.rs       # THE REAL DURABLE STORE — the SAME CommitRecord + the SAME chain gate, but
                          #   committed into real redb ACID tables (COMMIT_LOG, the two by-hash indices,
                          #   the metadata cursor + head) in ONE write txn over a StorageBackend. The
                          #   RegionBackend impls redb's block-device trait (len/read/set_len/sync_data/
                          #   write); on the host it is file-backed (REAL cross-process durability), and
                          #   the on-device persist PD swaps in a BlockCapBackend over the seL4 block cap
                          #   — the SAME five ops, the durable-store logic UNCHANGED. (8 #[test]s.)
  src/hosting.rs          # THE APP-HOSTING ECONOMY — pay coin to be hosted = a VERIFIED VALUE TURN:
                          #   an app (a cell with durable hosted state) pays a hosting fee to the host
                          #   cell per period (a conserving Transfer, app→host, committed through the
                          #   durable spine). A fee that lapses EVICTS the app (a verified, durable turn
                          #   dropping the hosting), fail-closed. Σ value invariant. (6 #[test]s.)
  src/main.rs             # the original pure chain-gate witness: the executor→persist→read spine +
                          #   all four anti-substitution teeth, as a binary AND 7 #[test]s
  src/durable_main.rs     # the durable + hosting witness binary: PART A drives the spine over REAL redb
                          #   with a persist-PD restart (drop + reopen the file → no turn lost); PART B
                          #   drives the hosting economy (pay-to-host conserving turns + an eviction).
  src/lib.rs              # exposes commit_store / redb_store / hosting so the binaries + tests share them
```

The crate is **standalone** (its own `target/`, not a member of `sel4/dregg-pd`'s
workspace) — swarm-safe, and it does **not** touch the root `./target`. **21 tests
pass** (`cargo test --release`: 14 lib + 7 binary; `test result: ok` on every
binary).

### 2.2a The durable store is REAL redb — and that is WHY it ports to seL4 unchanged

The advance over a `BTreeMap`: `redb_store.rs` is the persist PD's durable store in
real `redb` — the **same ACID store `persist/src/commit_log.rs` uses on a node**.
The chain gate, the `CommitRecord`, the one-transaction torn-state/idempotent
discipline are byte-for-byte `commit_store`'s (a refusal is the same `ChainRefusal`,
the head does not move on a refusal); the *only* new thing is that the commit lands
in a real redb write transaction whose `commit()` is the fsync boundary. So "durable"
is now real: the witness `commits_survive_drop_and_reopen_over_the_same_bytes`
commits two turns, **drops the store + backend**, reopens over the same file bytes,
and the head + cursor + log rows + by-hash indices all recover and the chain
self-checks — the durability the brief asked for, demonstrated.

The seam that makes this port to seL4 with the gate **unchanged**: redb stores
through a [`redb::StorageBackend`] — a trait of exactly five ops (`len` ·
`read(offset,len)` · `set_len` · `sync_data(eventual)` · `write(offset,data)`),
which is *precisely a raw block device's interface*. `RegionBackend` is that impl
over a fixed byte region; on the host it is file-backed (real durability), and **the
on-device persist PD's backend (`BlockCapBackend`, the named rung §3.3) is one
`StorageBackend` impl whose five ops go through the seL4 block cap it solely holds —
and the entire durable-store logic above it is unchanged.** That is the honest shape
of the remaining work: not a new store, a block-cap `StorageBackend` under the store
that already runs.

### 2.3 What it proves (run-verified, green)

`cargo run --release` (the binary) and `cargo test --release` (7 tests) both pass.
The witness drives the full spine:

```
[1] executor produced turn 7000 (ordinal 0, prev=GENESIS); persist committed at ordinal 0
[2] read returns the committed turn (by ordinal / by turn_hash / by receipt_hash all agree)   ← reads are free
[3] turn 7001 chains onto turn 7000 (prev_root == prior ledger_root); committed at ordinal 1   ← Tier-C chain
[4] light-client walk re-checks the on-store root chain -> INTACT                              ← self-checking
  admit(turn w/ wrong prev_root)   -> REFUSE (root mismatch: head 85b8fe2d != turn.prev_root ffffffff)
  admit(turn w/ ordinal gap)       -> REFUSE (integrity: expected ordinal 7 != durable cursor 2 …)
  admit(replay of committed turn0) -> ADMIT (ordinal 0) (idempotent)
  admit(different turn @ ordinal0) -> REFUSE (integrity: ordinal 0 already holds a different turn)
[5] persist-PD restart resumes at cursor 2 head 85b8fe2d (no turn lost)                        ← durable resume
== deos spine GREEN: a verified turn commits durably, a read returns it,
== and the chain gate refuses every non-chaining / out-of-order / forged turn
```

```
running 7 tests … test result: ok. 7 passed; 0 failed
  commit_then_read_returns_the_turn · turns_chain_through_the_head ·
  wrong_prev_root_is_refused_root_mismatch · ordinal_gap_is_refused ·
  replay_is_idempotent_collision_is_refused · restart_resumes_from_durable_head ·
  pure_chain_step_gate
```

The mapping from witness step → pg-dregg property:

- **[1]+[2]** = the spine's two halves: a write is a *verified-turn post-image*
  (the producer stamps the `(ordinal, prev_root)` the store hands it — the
  `pg-dregg/src/drainer.rs` `produce(intent, ordinal, prev_root)` contract), and a
  read is *free* (`lookup_by_*` = the `dregg.turns` row read, no writer touched).
- **[3]+[4]** = Tier C (`docs/PG-DREGG.md` §10): the chain tooth on the rows. A
  light client re-validating `prev_root[N+1]==ledger_root[N]` is the §10.1 / §15.1
  "self-checking projection" — the persist PD's store is a hash chain a replica can
  itself check.
- **the four teeth** = the `dregg.commit_log` trigger's refusals (`docs/PG-DREGG.md`
  §10.3's "honest failure mode": a gate that doesn't gate is the disease; here every
  non-chaining / gapped / replayed / colliding turn is refused, fail-closed).
- **[5]** = the durable resume (`persist`'s `commit_cursor()` recovery /
  `RootChain::resume`): a persist-PD restart reads the durable head + cursor and
  loses nothing — the *durability* half of "durable verified state."

### 2.4 The discipline is reused, not reinvented (the load-bearing claim)

`commit_store.rs` carries the pg-dregg gate **verbatim**, each piece cited to its
origin:

- the chain gate `verify_chain_step(head, next_ordinal, prev_root, ordinal) ->
  Result<(), ChainRefusal>` is the exact signature + logic of
  `pg-dregg/src/mirror.rs:477` — the gate the pg `dregg_verify_turn` SQL function
  runs and the `RootChain::extend` (`mirror.rs:418`) anti-substitution tooth. (The
  pg-side third refusal variant is `Malformed`; the persist organ names its
  torn-state variant `Integrity` for the durable-cursor checks, which are the
  `commit_finalized_turn_with_burns` integrity errors — the *gate semantics* are
  identical, fail-closed.)
- `CommitRecord` is `persist/src/commit_log.rs:82`'s record (ordinal · height ·
  block_id · turn_hash · creator · receipt_hash · ledger_root · touched_cells),
  plus the explicit `prev_root` that `pg-dregg`'s row carries so the chain is
  checkable on the rows alone.
- `commit_verified_turn` is the `commit_finalized_turn_with_burns`
  (`commit_log.rs:260`) one-transaction discipline: the `expected_ordinal == cursor`
  torn-state guard, the idempotent-replay branch (same `turn_hash` ⇒ no-op success;
  different ⇒ Integrity error), the append-then-index-then-advance-cursor-LAST
  ordering. On-device that synchronous block becomes one redb `commit()` over the
  block cap.

So the witness is not a parallel toy semantics — it is the **same gate** the live
pg-dregg + persist stack already enforces, lifted into the `no_std` shape the
persist PD will carry. That is the whole point: the persist PD enforces the SAME
spine the pg verified store does.

---

## 3. What's a prototype, what's a design, what's the wall (the honest verdict)

The same honesty discipline `sel4/crypto-floor-hosttest/` uses (the crypto floor:
host-test green, the on-device selftest-ELF run is the macOS checkpoint).

### 3.1 PROTOTYPE (runnable, green here)

- **The persist-PD chain-gate discipline** — `sel4/persist-hosttest/src/commit_store.rs`,
  green (§2.3). The executor→persist→read spine and all four anti-substitution teeth
  run on this box. It is `no_std`+`alloc`, ready to ride inside the persist PD by a
  `#[path]` include.
- **The REAL durable store in `redb`** — `redb_store.rs`, green. The SAME chain gate
  + `CommitRecord` + one-transaction discipline, but committed into real `redb` ACID
  tables over a block-device `StorageBackend`. Durability is *real*: a commit
  survives the store being **dropped + reopened** over the same file bytes (the
  `commits_survive_drop_and_reopen_over_the_same_bytes` tooth), the head/cursor/log/
  indices all recover, and the chain self-checks. This is the `BTreeMap`→durable
  promotion the brief asked for.
- **The app-hosting economy** — `hosting.rs`, green. Pay coin to be hosted is a
  conserving value turn (a `Transfer`, app→host, committed through the durable
  spine); a lapsed fee EVICTS (a verified, durable turn dropping the hosting),
  fail-closed; Σ value is invariant across every charge. (See §6.)

### 3.2 BOOTS (real on-device, independently)

- **The executor PD** runs the verified turn inside a real seL4 protection domain
  (`status:2 ok:1`, `docs/EMBEDDABLE-LEAN-RUNTIME.md` §4; `sel4/dregg-pd/executor-pd/`
  WALL.md "step 4 DONE: the verified executor runs INSIDE seL4"). The *writer* organ
  of the spine is not a design — it boots.
- **The five-PD assembly seat shape** (`sel4/dregg.system`): verifier (pri 100) ·
  executor (120) · persist (80) · net (60) · app (50), with the executor→persist
  `commit_out` (RW→R) handoff + the executor `turn_in` (R) ingress edge already
  wired as shared regions + notifications. The PD topology the persist organ slots
  into exists.

### 3.3 DESIGN (mapped, not yet built)

- **The `BlockCapBackend` — one `redb::StorageBackend` over the seL4 block cap** (the
  precise remaining rung, refined down from "the redb backend"). The redb durable
  store itself is now **host-green** (§2.2a, §3.1) — what is left is *one trait impl*:
  `RegionBackend`'s five ops (`len`/`read`/`set_len`/`sync_data`/`write`) become block
  reads/writes/flush over the raw block cap the persist PD solely holds (plus the
  snapshot⊕overlay + root tooth, `persist/src/snapshot.rs`). The durable-store logic
  above it — the chain gate, the one-transaction commit — is byte-for-byte unchanged.
  This is a *bounded* port (a device-driver trait impl), not the open-ended fog: the
  store that rides on it already runs.
- **The executor→persist commit-record transport** over `commit_out`. Today the seat
  reads a sentinel byte; the real path writes the serialized `CommitRecord` into
  `commit_out` and signals channel id 1, and the persist PD runs
  `commit_verified_turn` before the turn returns (the `n=1` synchronous-commit
  property, `docs/FIRMAMENT.md` §3). The record *shape* and the *gate* are fixed; the
  serialization + the shared-region framing are the work.
- **The submit-queue / ingress enqueue** (`docs/PG-DREGG.md` §11.4 on seL4): a
  confined component enqueues a signed turn over the net/ingress→executor `turn_in`
  edge; the executor PD is the gate (it may refuse), exactly as the
  `node/src/submit_queue_drainer.rs` drainer is on a node. The enqueue-not-execute
  shape is the seL4-native outbox.
- **The executor→persist commit-record transport** over `commit_out`. Today the seat
  reads a sentinel byte; the real path writes the serialized `CommitRecord` into
  `commit_out` and signals channel id 1, and the persist PD runs
  `commit_verified_turn` before the turn returns (the `n=1` synchronous-commit
  property, `docs/FIRMAMENT.md` §3). The record *shape* and the *gate* are fixed; the
  serialization + the shared-region framing are the work.
- **The submit-queue / ingress enqueue** (`docs/PG-DREGG.md` §11.4 on seL4): a
  confined component enqueues a signed turn over the net/ingress→executor `turn_in`
  edge; the executor PD is the gate (it may refuse), exactly as the
  `node/src/submit_queue_drainer.rs` drainer is on a node. The enqueue-not-execute
  shape is the seL4-native outbox.

### 3.4 THE WALL (named, with its lever)

- **The in-qemu boot of the executor-PD / persist-PD PAIR committing a turn over
  `commit_out`** is the named wall — *exactly* the crypto-floor pattern. On macOS
  there is **no user-mode `qemu-aarch64`** to run a single PD's logic in isolation
  (only `qemu-system-aarch64` for the full image boot), so the runnable witness is
  the host-test (§2), and the on-device checkpoint is a clean ELF link of the
  persist PD carrying `commit_store.rs` over redb, plus the full-image boot showing
  the executor seat → persist seat → committed-row over `commit_out`.
  **Lever:** the gate logic is host-green and `no_std`-portable; the persist PD's ELF
  link (the crypto-floor checkpoint shape) and the block-cap backend are the
  remaining on-device steps. None is the open-ended runtime fog the roadmap feared —
  the *runtime* port is the executor PD's, and it BOOTS.

The crisp verdict: **the spine's discipline is a green prototype + the writer organ
boots; the durable store is now REAL `redb` (host-green — a commit survives
drop+reopen), with one block-cap `StorageBackend` impl the only on-device rung; the
app-hosting economy (pay-to-host + eviction as conserving, fail-closed verified
turns) is host-green on top; the wall is the in-qemu PD-pair commit (the macOS
user-mode-qemu gap), not the semantics.**

---

## 4. Where pg-dregg-on-seL4 sits in the seL4 ambitions ladder

ember: *"lots of seL4ish ambitions!!!"* Here is the ladder, with this work's rung
marked, so the deos spine is located honestly among the rest
(`docs/EMBEDDABLE-LEAN-RUNTIME.md` §4, `docs/SEL4-EMBEDDING.md`,
`docs/FIRMAMENT.md`):

| Rung | Ambition | Status | This work |
|---|---|---|---|
| R0 | the verified turn runs inside a real seL4 PD | **BOOTS** (`status:2 ok:1`) | the writer organ the spine depends on |
| R1 | the crypto floor real for hashes + STARK verify + the live proof-carrying-turn admission | **host-test green, ELF links clean**; on-device selftest-ELF run = the macOS checkpoint (3 EC primitives stay fail-closed) | the pattern THIS doc follows |
| **R2** | **the persist-PD durable commit log + chain gate — the deos spine (reads-free/writes-verified/durable)** | **host-test GREEN (this work)**; in-qemu PD-pair commit = the wall | **← THIS DOC + `sel4/persist-hosttest/`** |
| **R3** | **the durable store in real `redb` over a block-device `StorageBackend` (durable: commit survives drop+reopen)** | **host-GREEN (this work, `redb_store.rs`)**; the on-device `BlockCapBackend` (one trait impl) = the named rung | **← the durable transport, now REAL redb; only the block-cap `StorageBackend` impl remains** |
| **R8** | **the app-hosting economy — pay coin to be hosted = a verified value turn; fee-lapse → eviction** | **host-GREEN (this work, `hosting.rs` + `Dregg2/Apps/HostingLease.lean`)** | **← the deos charge: conserving, fail-closed, the lease as a time+budget caveat** |
| R4 | the principled elaborator import-trim (so the elaborator is never pulled into the executor's module closure, vs no-op'd at init) | NAMED WALL (`docs/EMBEDDABLE-LEAN-RUNTIME.md` §4 item 2) | a productionization gate on R0 |
| R5 | the decomposed 5-PD Microkit assembly (cap-partition trust boundary), vs the booting root-task-with-std | DESIGN/seat (`sel4/dregg.system` is the shape; the executor boots as a root task) | the assembly the persist organ folds into |
| R6 | the virtio-net / smoltcp tail — the net PD as the sole NIC cap, the distributed/federation edge confined | partial (a real virtio NIC is brought up; the full stack is the tail) | the ingress/submit transport for §3.3 |
| R7 | literal Postgres as a confined VMM-guest PD (the full pg18 query engine, unmodified) | DESIGN ladder (`docs/PG-DREGG-ON-SEL4.md` paths 3a/3b/3c) | the *other* surface — a SQL face on the same spine |

**R2 is this work's rung**, and it sits cleanly on R0 (the writer boots) and below
R3 (the durable backend). It is *independent* of R4/R5/R6/R7 — the spine's gate
semantics are green now, regardless of the elaborator trim, the Microkit
decomposition, the net tail, or whether a literal Postgres ever joins. The deos
spine is the **discipline** rung: it proves the seL4 PD pair realizes pg-dregg's
"durable verified state" with the same gate the live pg stack runs, with the in-qemu
PD-pair commit as the one named wall.

---

## 5. Bottom line

| | Was | Now |
|---|---|---|
| "pg-dregg inside seL4" | read as "port Postgres into seL4" (heavy; the `PG-DREGG-ON-SEL4.md` VMM ladder) | **the persist-PD IS the commit log of the seL4 deos foundation** — the executor PD writes verified turns, the persist PD durably stores them, reads are free; the *discipline* crosses, not the C program |
| the persist PD | a SEAT that holds the place but stores nothing | its **durable verified commit log + chain gate** is written and **host-GREEN in real `redb`** (`redb_store.rs`) — a commit **survives drop+reopen** over the same bytes; the only on-device rung is one block-cap `StorageBackend` impl |
| the spine's organs | — | the **executor PD BOOTS** (writer); the **persist store is host-green in real redb** (durable); the **app-hosting economy is host-green on top** (pay-to-host + eviction, conserving, fail-closed); the wall is the in-qemu PD-pair commit (the macOS user-mode-qemu gap), not the semantics |

The deos foundation is the discipline — reads-free, writes-verified, durable —
realized by the executor-PD / persist-PD pair. The persist PD runs byte-for-byte the
pg-dregg chain gate, so the seL4 store and the pg `dregg.turns` are the same store
with two faces; and that store is now real `redb` whose `commit()` is the fsync
boundary, so "durable" is demonstrated, not promised. On top of it the deos OS
**charges coin to host apps** — a verified value turn — and evicts a lapsed app
fail-closed. The writer boots; the store is green and durable; the economy is green;
the one wall is named, with its lever, and it is the same macOS user-mode-qemu
checkpoint the crypto floor already lives behind.

---

## 6. The app-hosting economy — pay coin to be hosted is a verified value turn

ember: *"deos/sel4 needs pg-dregg to host apps — and maybe charge coin for
hosting."* The deos OS hosts apps; hosting them costs coin. That charge is **not a
side-ledger** — it is a verified value turn through the very spine §1–§3 built, so a
hosting payment is durable, ordered, conserving, and self-checking like every other
turn. Built + green: `sel4/persist-hosttest/src/hosting.rs` (the runtime, over the
real durable store) + `metatheory/Dregg2/Apps/HostingLease.lean` (the proof).

### 6.1 The model

An **app is a cell with durable hosted state in the persist-PD** (its rows live in
the same commit log as everything else — the deos spine). Per **hosting period** the
app **pays a fee in coin to the host cell**: a real value move — the `turn`-crate
`Effect::Transfer { from, to, amount }` (conservative linearity,
`turn/src/action.rs:819`) — coin LEAVES the app cell and ARRIVES at the host cell, Σ
value unchanged. It commits as a verified turn through the durable store (the chain
gate admits it; the log records it). When the fee **lapses** (the app's prepaid
balance cannot cover the period's fee) the host **EVICTS** the app: a verified turn
drops the app's durable hosting, fail-closed — *non-payment cannot buy free
hosting*. A paid app's state persists. Each charge and each eviction is a durable row.

### 6.2 The hosting lease — a cap with a TIME + BUDGET caveat over the durable slot

The lease is exactly that: a capability to occupy a durable hosting slot, bounded by
a **budget** (the prepaid balance) and a **time window** (the paid-through period).
`Dregg2/Apps/HostingLease.lean` proves it as a four-caveat `RecordProgram` charge
gate (each a `StateConstraint`, each a both-polarity theorem, `#assert_all_clean`):

| caveat | atom | what it enforces | tooth |
|---|---|---|---|
| **provenance** | `senderInField host` | only the recorded host may collect the fee | `impostor_charge_rejected` |
| **the BUDGET** | `balanceGe leaseFee` | the app's balance must cover the fee — *an unfunded app's charge is UNSAT, the eviction trigger* | `lapsed_app_charge_rejected` |
| **the FEE FLOOR** | `balanceDeltaGe (−leaseFee)` | the host may not debit more than the agreed fee | `over_charge_rejected` |
| **the TIME window** | `strictMono period` | the billing period strictly advances — no double-bill | `replayed_period_rejected` |

and the gate is non-vacuous — the honest charge (host-signed, app funded, exact-fee
debit, next period) COMMITS (`honest_charge_admits`). The lapsed-fee tooth is the
load-bearing one: a charge against an app that cannot pay is *unsatisfiable*, so the
runtime takes the eviction branch — the lease's budget caveat **forces** eviction
when the budget is gone.

### 6.3 What the Rust realization proves (green, over REAL durability)

`hosting.rs`'s six `#[test]`s run over the real `redb` durable store:

- **`a_hosting_charge_is_a_conserving_transfer`** — a fee charge debits the app,
  credits the host, and Σ value is unchanged (a `Transfer`, not a mint).
- **`a_lapsed_app_is_evicted_a_paid_app_persists`** — the eviction tooth: a funded
  app pays every period and stays hosted; an app whose balance runs dry is EVICTED
  (fail-closed) the first period it cannot pay.
- **`eviction_is_a_durable_ordered_verified_turn`** — the eviction is a committed row
  in the durable log (the `Evict` tag, the app as creator) and the chain self-checks
  across it.
- **`value_conserved_across_a_full_hosting_run`** — Σ value equals the genesis supply
  after *every* charge across a multi-app, multi-period run (hosting charges coin,
  never forges it).
- **`top_up_cannot_overdraft_the_funder`** — funding a lease cannot forge value (no
  overdraft).
- **`hosting_survives_a_persist_pd_restart`** — the whole hosting history survives a
  persist-PD restart (drop + reopen the durable store over the same bytes).

So the deos OS's "charge coin to host apps" is a verified value turn on the durable
spine: conserving, fail-closed on non-payment, durable, and self-checking — the
economy is the spine, not a bolt-on.

---

## 7. The honest frontier — the doc's two answers, and which path this took

The brief's two paths, stated plainly so the frontier is not blurred:

- **Full Postgres-in-libvmm** (`docs/PG-DREGG-ON-SEL4.md`): run the literal 1.5-M-line
  pg18 C program as a confined VMM-guest PD (a Linux guest under libvmm). This is the
  *other* surface — a real SQL query engine confined in seL4 — and it stays a DESIGN
  ladder (paths 3a/3b/3c there). It is heavy, and it is not what "host apps + charge
  coin" needs.
- **The persist-PD-as-postgres path** (THIS doc): the persist PD's `redb` commit log
  IS the `dregg.turns` of the deos OS; the executor PD is its writer; reads are free;
  hosting is a verified value turn on it. This is the path taken — and it is now
  **host-green with real durability + a working economy**, with one bounded on-device
  rung (the block-cap `StorageBackend`) and the in-qemu PD-pair commit as the named
  wall. No Postgres is required to host apps and charge for hosting; the *discipline*
  is what the deos OS runs.

Both surfaces share one spine (reads-free / writes-verified / durable); this doc
realized the spine natively in the PD pair and built the hosting economy on it,
because that is what "deos/sel4 needs pg-dregg to host apps" actually asks for.

*( ◕‿◕ ) the spine holds: a verified turn commits durably (in real redb), a read
returns it, every non-chaining turn is refused — and hosting an app costs coin (a
conserving value turn), a lapsed fee evicts, fail-closed. In a PD pair, no Postgres
required.*
