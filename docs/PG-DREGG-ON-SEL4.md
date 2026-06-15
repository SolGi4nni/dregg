# PG-DREGG-ON-SEL4 — embedding Postgres into the robigalia/seL4 dregg OS as a confined component

*Design + scoping doc. Present-tense where the pieces are real (the submit-queue
drainer, the Tier-A/B/C mirror, the five-PD assembly that boots, the verifier PD,
the executor PD's one-turn heartbeat); clearly-scoped research where it is not
(native-seL4 Postgres). First-principles, no trajectory narrative. The safety
argument is the spine: it is stated first and kept load-bearing at every turn.
Every seam is named as work with a closure lever, never a wall; nothing is
overclaimed. Companion to `docs/PG-DREGG.md` (the Tier ladder + the spine
invariant), `docs/PG-DREGG-PG18.md` (the feature set), `docs/ROBIGALIA-ROADMAP.md`
(the PD model + the Lean-runtime status), and `docs/SEL4-EMBEDDING.md` (the
blockers). Cites the tree as of 2026-06-13.*

ember's framing: *some operating systems embed SQLite (fine); some embed Postgres
(wao, so powerful).* This doc is how dregg-OS embeds Postgres — the whole pg18
query engine, RLS-caps, federation-via-replication, the verified write loop — as a
**confined** seL4 component that **never enters the trusted base**.

> **Companion (the OTHER surface).** This doc embeds the *literal* Postgres C
> program as a confined component (the VMM-guest ladder, §3). Its companion,
> `docs/PG-DREGG-ON-SEL4-DEOS-SPINE.md`, takes the dual view: pg-dregg's *model* is
> "durable verified state" (reads-free / writes-verified / durable), and the seL4
> world already realizes that discipline **natively** in the executor-PD / persist-PD
> pair — the persist PD *is* the `dregg.turns` commit log of the seL4 deos
> foundation, no Postgres port required. That doc ships a green host witness
> (`sel4/persist-hosttest/`) for the executor→persist→read spine + the Tier-C chain
> gate. The two docs are the two faces of "your node IS your postgres": a SQL face
> (here) and the native PD-pair spine (there).

---

## 0. The thesis, in one paragraph

Postgres is a roughly 1.5-million-line unverified C program. Embedding it into a
*formally-verified* object-capability OS sounds like a contradiction — until you
see that **dregg-OS never puts Postgres in the trusted base**, by two composing
mechanisms that this doc makes airtight. (1) Postgres is **confined**: it runs in
its own seL4 protection domain whose entire authority — storage, network, IPC,
every syscall — is the set of capabilities its parent handed it. The
machine-checked microkernel mediates *every* syscall; Postgres touches only what
its PD holds, nothing ambient. (2) Postgres's **writes to authoritative dregg
state are gated by the verified executor**: the executor PD is the *sole* writer of
kernel-authoritative state, and Postgres can only *enqueue a signed turn* (the
`dregg_submit_turn` → `dregg.submit_queue` → the drainer in
`node/src/submit_queue_drainer.rs` → the verified executor, which validates and is
free to refuse). So Postgres is a **queryable projection plus a submission queue**,
never the trust boundary. Its size and un-verifiedness cannot corrupt verified
state; the worst it can do is serve a stale read or drop a submission. And **two
capability layers compose**: the SQL RLS-caps decide *which rows* a reader may
read, while the seL4 caps decide *what the Postgres PD may touch at all* — a dregg
capability inside a seL4 capability, the same abstraction at two scales.

---

## 1. The spine — why a 1.5M-line C program never enters the trusted base

This is the load-bearing argument of the whole doc, and everything else is a
consequence of it. State it precisely, then defend each clause.

> **THE SAFETY SPINE.** Embedding Postgres in dregg-OS is sound — adds **zero** to
> the verified trusted base — because Postgres is (a) **confined** to a seL4 PD
> whose every syscall the machine-checked microkernel mediates, so it touches only
> the capabilities it was handed; and (b) **write-gated** by the verified executor,
> the sole writer of authoritative state, so Postgres can only *enqueue a signed
> turn* the executor independently validates. Postgres is therefore a **queryable
> projection + a submission queue**, not a trust boundary: its worst failure is a
> stale read or a dropped submission, never a forged state transition.

### 1.1 The trusted base, named precisely

dregg-OS's trusted computing base is small and enumerable:

- **the seL4 microkernel** — ~10 kLOC of C, machine-checked (functional
  correctness + integrity + confidentiality), the only thing with hardware
  authority;
- **the verified executor PD** — the compiled Lean `execFullForestG` +
  admission (`dregg_exec_full_forest_auth`, proved in `metatheory/`), the sole
  authority over state transitions;
- **the verifier PD** — independent proof-checking, no prover authority (a real
  STARK runs on-device today, `sel4/dregg-pd/verifier-stark/`);
- the thin **cap-partition** that wires them (the Microkit `.system` assembly /
  CapDL spec, itself a checkable artifact, `docs/ROBIGALIA-ROADMAP.md` §7).

**Postgres is not in that list, and the architecture is what keeps it out.** It
is a *confined component* whose presence the trusted base neither trusts nor
depends on for any safety property. The verified guarantees (conservation,
no-amplification, nullifier-uniqueness, authenticated root evolution) are
properties of the executor's transition function — they hold *whether or not*
Postgres is present, correct, or compromised.

### 1.2 Clause (a) — CONFINEMENT: the microkernel mediates every syscall

On a seL4 microkernel a protection domain has **no ambient authority**. It cannot
open a file, touch a device, send on a socket, or read another PD's memory unless
it holds an seL4 **capability** to do so, and *every* such action is a kernel
invocation the microkernel checks against the PD's c-space. This is the exact
property `docs/ROBIGALIA-ROADMAP.md` §1 builds the OS on: each PD "cannot reach a
clock, RNG, socket, device, or another app's memory — ambient authority is
*structurally absent* (the MMU + the cap-derivation tree enforce it)."

For the Postgres PD this means its **entire** interaction surface is enumerable
and parent-granted:

- **storage** — Postgres reaches its data directory only through whatever
  storage capability the parent handed it (mediated, near-term, by the persist PD
  or the seL4 VMM's virtio-block backend, §3a). No raw disk; no other PD's store.
- **network** — Postgres's listener and any logical-replication connection reach
  the wire only through the net PD that solely holds the NIC cap
  (`docs/ROBIGALIA-ROADMAP.md` §5). Postgres cannot open a socket the net PD did
  not mediate (§4.4).
- **IPC** — Postgres talks to the rest of the OS only over the seL4 endpoints its
  c-space contains: the channel to the executor PD (to enqueue), and the channel
  the mirror writes arrive on. There is no other path.
- **syscalls** — there is no `syscall` Postgres can make that the microkernel does
  not mediate against its caps. A compromised Postgres cannot escalate, because
  there is no ambient kernel surface to escalate *through*.

So even a fully-popped Postgres (RCE, the worst case for a C program of this size)
is **contained by construction**: it is a process in a box whose walls are
kernel-checked capabilities. It can corrupt *its own* projection of state; it
cannot reach past its c-space. This is precisely why a microkernel OS can embed a
huge unverified program at all — the same reason `docs/EMBEDDED-WEB-SURFACE.md`'s
renderer PD can run Servo, or the seL4 VMM can host an entire Linux guest: the
blast radius is the PD's capability set, full stop.

### 1.3 Clause (b) — WRITE-GATING: the executor is the sole writer of truth

Confinement alone bounds the damage to "Postgres's own memory and the caps it
holds." The second mechanism makes even *that* unable to touch authoritative
state, by enforcing the **spine invariant** of `docs/PG-DREGG.md` §8 at the OS
level:

> **Reads are free SQL; state mutates ONLY through verified turns.**

The verified executor PD is the **sole writer** of kernel-authoritative state
(`docs/ROBIGALIA-ROADMAP.md` §1: "the verified semantics is the *only* authority
over state transitions"). Postgres holds **no capability** that lets it mutate
authoritative state directly — there is no "write the ledger" cap in its c-space.
What Postgres *can* do is **enqueue a signed turn**: a pg role calls
`dregg_submit_turn(signed_turn, agent)`, which records an *intent* into
`dregg.submit_queue` (RLS-gated, §4.2). That intent is drained by
`node/src/submit_queue_drainer.rs`, which hands it to **the one executor gate**
(`execute_via_producer`, #171) — the same verified producer every ingress uses —
and the executor independently re-checks the signature, the agent derivation, the
receipt chain, and the full turn semantics, and is free to **refuse**.

The drainer's own doc-comment states the property exactly
(`node/src/submit_queue_drainer.rs`):

> *Postgres never executes — `dregg_submit_turn` only records an intent. The
> drainer hands that intent to the REAL verified executor (the same one every
> ingress uses), so the executor stays the sole trust boundary; the drainer is
> plumbing, not a second semantics. A queued turn the executor rejects is recorded
> `refused` and changes no state.*

So a malicious or buggy Postgres that enqueues a forged, amplifying, or
double-spending turn achieves **nothing**: the executor rejects it and the
`submit_queue` row resolves to `refused`. Postgres cannot forge a receipt, cannot
skip the executor, cannot present a turn the signing key did not sign. The
**worst-case** is exactly two failure modes, both benign:

1. **a stale read** — Postgres's *projection* of state lags or (if corrupted)
   disagrees with the authoritative ledger. A reader sees old or wrong *query
   results*; no authoritative state moved. (And the projection is itself
   self-checking: the Tier-C chain tooth, §2.3, lets even a replica detect a
   diverged mirror.)
2. **a dropped submission** — a turn a pg-user tried to submit never reaches the
   executor (Postgres crashed, the queue row was lost). The user's action did not
   happen; nothing *false* happened. And the drainer resumes from the `pending`
   rows on restart, so a crash between enqueue and drain loses nothing
   (`submit_queue_drainer.rs`: "a node restart resumes from the `pending` rows,
   losing nothing").

Neither failure mode can violate a single verified guarantee, because neither
produces a state row that is not a verified-turn post-image. **That is the spine.**

### 1.4 The two composing capability layers

The embedding earns its safety from **two capability systems stacked**, each
mediating a different question, and it is worth seeing them as one gradient rather
than two mechanisms:

| Layer | The capability | The question it answers | Enforced by |
|---|---|---|---|
| **SQL RLS-caps** (dregg-auth) | a `dga1_…` credential in the `dregg.token` GUC | *which rows* may this reader read / *which turns* may this role enqueue? | the Postgres RLS engine calling the verified `dregg-auth` decision (`docs/PG-DREGG.md` §1–§6) |
| **seL4 caps** | the CNode/endpoint/frame/device caps in the Postgres PD's c-space | *what may the Postgres PD touch at all* (disk, wire, which IPC endpoints)? | the seL4 microkernel mediating every syscall (`docs/ROBIGALIA-ROADMAP.md` §1) |

These are the **same abstraction at two points on the distance parameter `n`**
(`docs/ROBIGALIA-ROADMAP.md` §8, `docs/FIRMAMENT.md` §3): an seL4 cap and a dregg
cap are both unforgeable, attenuable, delegable references; they differ only in how
far the resource is. The seL4 caps confine the *container* (Postgres-the-PD); the
dregg RLS-caps gate the *content* (which rows flow through it). A reader must
satisfy **both**: the seL4 layer lets the query reach Postgres's memory at all, and
the RLS layer narrows the result to the rows its dregg capability admits. Defeating
one does not defeat the other — an attacker who somehow read Postgres's raw pages
(defeating RLS) still cannot exfiltrate them past the PD's c-space (the seL4 layer),
and an attacker who escaped the PD (defeating seL4 confinement — which requires
breaking the machine-checked kernel) finds only a *projection*, never the authority
to write truth. The composition is the safety, and it degrades gracefully: a breach
of either layer is bounded by the other.

---

## 2. The architecture — PD topology and where each pg-dregg piece sits

The embedding slots into the five-PD assembly that already boots
(`docs/ROBIGALIA-ROADMAP.md` §1, `make run-assembly`) by adding the Postgres PD as
a confined component beside the existing seats. The authoritative dataflow is a
loop: the **executor PD** is the source of truth; its verified-turn output is
**mirrored** into Postgres as a queryable projection; and a pg-user's write
travels **back** through the executor via the submit queue.

### 2.1 The PD topology

```
        ┌─────────────────────────────────────────────────────────────────┐
        │  dregg-OS  (Microkit assembly; seL4 cap-partition = trust bdry)  │
        │                                                                  │
        │   ┌──────────┐  commit_out   ┌──────────┐                        │
        │   │ executor │ ────────────▶ │ persist  │  (sole storage-dev cap)│
        │   │   PD     │  (RW → R)     │   PD     │                        │
        │   │ VERIFIED │               └────┬─────┘                        │
        │   │  TRUTH   │ ◀── turn_in ──┐    │                              │
        │   └────┬─────┘  (R)          │    │ mirror feed                  │
        │        │                     │    ▼  (verified-turn post-images) │
        │        │ verdict-ready       │  ┌──────────────────────────────┐ │
        │        ▼ (one-way)           │  │      POSTGRES PD             │ │
        │   ┌──────────┐               │  │  (CONFINED · NOT TRUSTED)    │ │
        │   │ verifier │               │  │                              │ │
        │   │   PD     │               │  │  Tier-B mirror (cells/turns/ │ │
        │   │ STARK ✓  │               │  │    caps/memory — read-only)  │ │
        │   └──────────┘               │  │  RLS-caps gate every read    │ │
        │                              │  │  range-attest SRFs           │ │
        │   ┌──────────┐               │  │  dregg.submit_queue ─────────┼─┘
        │   │  net PD  │  (sole NIC    │  │    (enqueue signed turns)    │
        │   │ virtio   │   cap; the    │  └──────────────┬───────────────┘
        │   │  + sDDF  │   ONLY wire)  │                 │  drained by
        │   └────┬─────┘               │                 ▼  submit_queue_drainer.rs
        │        │ mediates pg's       │          ┌─────────────┐
        │        │ listener + repl     └─────────▶│ THE ONE     │ executes via
        │        ▼ (§4.4)                         │ EXECUTOR    │ producer (#171)
        │   (the wire)                            │ GATE        │──▶ back to executor PD
        │                                         └─────────────┘    (validates / refuses)
        └─────────────────────────────────────────────────────────────────┘
```

The arrows that matter for safety: the **mirror feed** is one-directional
(executor → persist → Postgres), so Postgres only ever *receives* verified state;
and the **submit-queue path** routes every pg-originated write *back through the
executor gate*, so Postgres never writes truth directly. Postgres holds no
`commit_out` (RW) cap — it is downstream of the truth, never a writer of it.

### 2.2 Where each pg-dregg piece sits

The pg-dregg design (`docs/PG-DREGG.md`) maps onto this topology piece by piece.
Each lives *inside* the confined Postgres PD; none of them is in the trusted base,
and each composes with the spine:

- **Tier-A RLS-caps** (`dregg_cap_admits`, the `dregg.token` GUC) — the read gate
  on every state table. A reader sees only the rows its dregg capability admits.
  This is pure `dregg-auth` (offline, circuit-free), so it runs inside the
  Postgres PD with no extra OS authority. It is the **content** layer of §1.4.
- **Tier-B mirror** (`dregg.cells / turns / capabilities / memory`) — the
  queryable projection of the executor's verified output. It is **read-only to
  applications** by privilege construction (`docs/PG-DREGG.md` §9.3:
  `REVOKE … FROM PUBLIC`, `FORCE ROW LEVEL SECURITY`, the
  `dregg_reader`/`dregg_kernel` split). The *only* writer is the mirror feed —
  the kernel role, fed from the executor's commit path. So no application SQL can
  forge a state row, before any trigger fires; the spine holds by the privilege
  model. (On seL4 the mirror feed arrives over the executor→persist→Postgres IPC
  path, §2.3.)
- **range-attest SRFs** (`dregg_attest_range`, `docs/PG-DREGG.md` §10.2.1) — the
  read-side proof surface: a whole-chain IVC proof attesting that a *range* of
  turns executed correctly, surfaced as a set-returning function. Fail-closed (a
  refusal returns zero rows). Pure verification, no execution — it composes with
  the verifier PD's role (independent proof-checking).
- **federation-via-replication** (`docs/PG-DREGG.md` §15) — a subscriber Postgres
  tails a publisher's `dregg.turns` hash chain and **re-validates locally**
  (`revalidate_replicated_chain`), refusing a substituted/reordered/gapped stream.
  Its network cap is mediated by the net PD (§4.4), so the replication connection
  is itself confined.
- **the submit-queue drainer keystone** (`node/src/submit_queue_drainer.rs`) — the
  write loop's return path. Lives node-side (in the executor PD's world, not
  Postgres's), reads `dregg.submit_queue`, and executes each intent through the one
  verified executor gate. This is the piece that makes Postgres a *submission
  queue* rather than a writer of truth (§4.3).

### 2.3 The mirror feed on seL4 — the executor → persist → Postgres path

On the Linux/macOS node today the mirror is fed by a sink in the commit path
(`node/src/pg_mirror.rs`'s `PgSink`, the `pg-mirror-live` feature) that upserts each
verified `CommitRecord` into Postgres over `tokio-postgres`
(`docs/PG-DREGG.md` §9.2, B1). On seL4 the same projection rides the existing
control-flow edge — the executor PD already signals the persist PD over
`commit_out` when a turn commits — extended with one hop to the Postgres PD:

- the **executor PD** writes the verified post-state to `commit_out` (it already
  does — this is the one-turn heartbeat's `status:2 ok:1` path,
  `docs/ROBIGALIA-ROADMAP.md` §3);
- the **persist PD** (or the executor PD directly, a topology choice) forwards the
  touched-cell post-images to the Postgres PD over a dedicated IPC endpoint;
- the **Postgres PD** materializes them via the same `dregg.merge_cell` applicator
  the live node uses (`docs/PG-DREGG-PG18.md` §7) — by construction identical to
  the node's mirror writer, because it is literally the same SQL function.

The feed is **one-way** (truth flows *to* Postgres), so this hop adds no write
authority to Postgres. And the **Tier-C chain tooth** rides along: the mirror feed
carries `prev_root`/`ledger_root`, and the Postgres-side `dregg_verify_turn`
re-validates that turn *N*'s root chains onto turn *N+1*'s
(`docs/PG-DREGG.md` §10) — so even the *projection* is self-checking, and a
tampered mirror (a Postgres that corrupted its own tables) is detectable by a light
client walking `dregg.turns`. This is the seL4-native form of the "a replicated
mirror re-validates, it does not trust" property (`docs/PG-DREGG.md` §15.1).

> **Seam (the mirror IPC):** the executor→Postgres post-image hop is a new IPC
> endpoint in the assembly, not yet wired (the §3a/§3b realization paths below
> determine its concrete shape — a virtio/socket bridge to a guest Postgres, or an
> in-process call to a linked one). **Lever:** it is the same `CommitRecord`
> projection the live `PgSink` already performs; the work is the *transport*
> (an seL4 endpoint instead of a TCP connection), not the projection logic.

---

## 3. The three realization paths, honestly scoped

There are three ways to make "Postgres runs inside dregg-OS" real, at increasing
depth and decreasing near-term feasibility. They are **not** competitors — they are
a ladder, and the near-term path is genuinely buildable on the substrate that
exists today, while the purist path is honest research. The safety spine (§1) holds
in **all three**: each one keeps Postgres confined and write-gated; they differ only
in *how* Postgres is confined and *where* the executor sits relative to it.

| Path | What Postgres runs as | Executor relationship | Confinement mechanism | Feasibility |
|---|---|---|---|---|
| **(a) NEAR-TERM** | unmodified Postgres in a minimal **Linux guest** under the seL4 VMM | separate executor PD; writes via submit queue across the VMM boundary | the **VMM + virtio**: the guest touches only the virtio devices dregg mediates | **buildable on today's substrate** (the VMM exists; not production-ready) |
| **(b) DEEP (Tier-D)** | Postgres **with the executor linked in-process** (one PD holds DB + verified executor) | *same* PD; one txn mutates kernel state AND app tables atomically | the seL4 PD around the combined process | **gated on the Lean-runtime port** (shared with the executor PD blocker) + the pg/Lean process-model spike |
| **(c) PURIST** | **native-seL4 Postgres** via a Genode-style POSIX personality | separate executor PD (or linked, as (b)) | a native seL4 PD; no guest, no VMM | **long-term research** (the nanos precedent shows it *can* run on a minimal kernel; fork/shmem/process-model are real challenges) |

### 3a. NEAR-TERM — Postgres as a confined Linux-guest PD under the seL4 VMM

**The proposition.** Run **unmodified** Postgres (the real 1.5M-line C program,
exactly as upstream ships it, pg18) inside a *minimal Linux guest* that is itself a
single seL4 protection domain under the seL4 virtual-machine monitor. dregg-OS
hands that guest a deliberately small set of virtio devices, and *those caps are the
guest's entire authority.* Postgres inside the guest believes it is on Linux; the
seL4 layer underneath confines the whole guest to the virtio devices dregg chose to
expose.

**The substrate exists.** The seL4 VMM is **libvmm** (the au-ts Microkit VMM,
`github.com/au-ts/libvmm`), the current seL4-Foundation virtual-machine monitor: it
boots a guest OS as a Microkit PD, with **virtio net / block / console** backends
provided through **sDDF** (the seL4 Device Driver Framework; the VMM support library
ships virtio PCI / console / net, and sDDF is being extended to a device-
virtualization framework for sharing devices between VMs and native components). As
of 2026-06, libvmm **supports AArch64 only, with RISC-V support in development**
(`github.com/au-ts/libvmm`, accessed 2026-06-13). The crucial fit: **this is the
same shape `docs/ROBIGALIA-ROADMAP.md` already uses** — that roadmap's net PD
already runs a virtio-net driver over sDDF-shaped rings, and the assembly is already
a Microkit assembly of PDs. A Linux-guest VMM PD is an *additional seat in the same
assembly*, fed virtio devices by the same sDDF machinery. (libvmm is explicitly
**not production-ready** — its own README states it is "in-development and frequently
changing, and is not ready for production use," accessed 2026-06-13 — named honestly
as a maturity caveat, not a wall; §5. A related verification nuance: Microkit always
uses seL4's **MCS configuration**, whose proofs are still completing — scheduled
RISC-V 2026 / AArch64 2027 per the Microkit platform docs — so the *machine-checked*
floor under a Microkit assembly is the MCS kernel as that verification lands.)

**How confinement holds (clause (a) of the spine).** The guest's authority is
*exactly* the virtio devices the VMM PD exposes, and each of those is backed by a
real seL4 cap held by a driver PD:

- **storage** — the guest's Postgres data directory is a **virtio-block** device
  backed by sDDF, ultimately the persist PD's storage cap. Postgres writes its
  pages to a block device dregg controls; it cannot reach any other storage.
- **network** — the guest's NIC is a **virtio-net** device bridged through the net
  PD that solely holds the real NIC cap (§4.4). Postgres's listener and any
  replication connection reach the wire only through that bridge.
- **console / control** — a **virtio-console** for logs/health; no general syscall
  surface to the host, because the guest *is* a VM — its "syscalls" are guest-kernel
  syscalls confined to guest memory, and its only escape to the rest of dregg-OS is
  the virtio rings the VMM mediates.

So a fully-compromised Postgres-in-guest is contained by the VMM's virtio boundary
*on top of* the seL4 cap partition: the worst it reaches is the virtio devices, each
of which is a dregg-mediated cap. This is the standard, well-trodden "run untrusted
Linux software in a confined VM on seL4" pattern. **libvmm** (the Microkit VMM) is
the current Microkit-native form; **CAmkES-VM** (the older seL4 VM framework, the
`camkes-vm` project) is the established precedent that confined Linux guests on seL4
are a solved category, not a novelty — dregg's choice of libvmm is because the rest
of the assembly is already Microkit, not because the VM-on-seL4 idea is unproven.

**How write-gating holds (clause (b) of the spine).** The executor stays a
**separate PD** outside the guest. A pg-user's write is an `INSERT` into
`dregg.submit_queue` *inside the guest's Postgres*; the drainer reads that queue
across the VMM boundary (over the virtio-net/console channel, or a dedicated virtio
device) and executes each intent through the one executor gate in the executor PD.
Postgres-in-guest never holds a cap to the executor's `commit_out`; it can only
enqueue. The submit queue *is* the airlock between the confined guest and the
verified core.

**Why this is the near-term path.** It runs **unmodified upstream Postgres** — no
port, no fork, no POSIX-personality work — so the entire pg-dregg surface
(`docs/PG-DREGG.md`, `docs/PG-DREGG-PG18.md`: RLS-caps, the Tier-B mirror, the
range-attest SRFs, `MERGE … RETURNING old/new`, `uuidv7`, the lot) works *as-is*,
because it is the same Postgres those features target. The only new work is the
**transport plumbing** (the mirror feed and the submit-queue drain across the VMM
boundary) and **standing up the VMM seat** — both bounded, both on the substrate
that already boots. It is the honest "embed Postgres now" answer.

> **Seam (VMM maturity):** libvmm is not production-ready (seeded research). For a
> near-term *demo/devnet* the maturity is acceptable (the guest is confined
> regardless of VMM polish — a buggy VMM is still bounded by the seL4 caps it
> holds). **Lever:** track libvmm upstream; the confinement argument does not
> depend on the VMM being bug-free, only on the seL4 cap partition being correct
> (which is the machine-checked part).
> **Seam (guest weight):** a Linux guest + Postgres is heavy (hundreds of MB,
> a guest kernel). **Lever:** a *minimal* Linux (a buildroot/initramfs with only
> what Postgres needs) keeps it small; this is the standard appliance-VM discipline.

### 3b. DEEP — Tier-D: the executor linked IN-PROCESS into Postgres

**The proposition.** This is `docs/PG-DREGG.md` §11 (Tier D, "the AWESOME endgame")
realized on seL4. **One** PD holds *both* Postgres *and* the verified Lean executor,
linked in-process, so

```sql
BEGIN;
  SELECT dregg_submit_turn(pay_invoice);   -- the verified executor runs IN the backend
  UPDATE invoices SET paid = true;          -- the app's own rows
COMMIT;                                      -- kernel state AND app tables, ONE atomic txn
```

commits the dregg turn and the application's own rows **together or not at all**.
At this point *postgres IS a dregg node* (`docs/PG-DREGG.md` §11.2), with the unique
win Tier C and the sidecar cannot offer: **atomicity across kernel state and app
data.**

**Why it is still sound.** The executor inside the backend is *the same verified
executor* (`dregg_exec_full_forest_auth`, the machine-checked transition function);
so `dregg_submit_turn` produces *only* verified post-state, and the spine holds
because **the writer is literally the kernel** (`docs/PG-DREGG.md` §11.2). The PD
boundary still confines the combined process from the rest of dregg-OS (clause (a)),
and now clause (b) is satisfied *internally* — there is no submit queue because the
verified executor is in the same address space and runs synchronously. This is the
*strongest* form of write-gating: the gate is the kernel itself, in-process.

**The shared blocker.** Tier-D-on-seL4 inherits **the** historical blocker of the
whole robigalia roadmap — **porting the Lean runtime into an seL4 userland**
(`docs/SEL4-EMBEDDING.md` §2, `docs/ROBIGALIA-ROADMAP.md` §3). The verified
executor is compiled Lean linked against `libdregg_lean.a` + the Lean runtime
(leanrt, GMP, the libuv-driven IO loop the pure executor never uses, the C++
runtime). That port has been **driven to a one-turn heartbeat** — the verified turn
runs inside a real seL4 PD under QEMU (`status:2 ok:1`, byte-identical receipt,
`docs/ROBIGALIA-ROADMAP.md` §3) — but it is **not yet a service** (the crypto floor
is stubbed, the loop runs one turn and exits, the runtime shape is root-task not a
Microkit PD). Tier-D-on-seL4 sits *downstream* of carrying that heartbeat to a
service: you cannot link the Lean executor into the Postgres PD until the Lean
runtime runs as a steady-state seL4 component.

**A second, independent hazard.** Even with the Lean runtime ported, Tier D has the
process-model hazard `docs/PG-DREGG.md` §11.3 names: Postgres uses
`setjmp`/`longjmp` for error handling, and a Lean runtime mid-stack during a longjmp
unwind is a technical hazard that needs a **spike** to clear. On seL4 this hazard is
*not removed* by the PD boundary (it is internal to the combined process), so the
same spike is required. **D-sidecar** (`docs/PG-DREGG.md` §11.3) is the de-risked
alternative that sidesteps it: Postgres hands the envelope to a co-located executor
PD over an seL4 endpoint and the executor PD executes — which is *exactly* path
(3a)'s submit-queue shape, generalized. So on seL4, **path (3a) is the natural
D-sidecar**: SQL submit ergonomics, the executor in its own PD, ~75% of the Tier-D
payoff minus the single-transaction atomicity, with no Lean linked into Postgres.

> **Seam (Lean-in-pg on seL4):** the in-process executor wants (i) the Lean runtime
> as a steady-state seL4 component (shared with `docs/ROBIGALIA-ROADMAP.md` §3's
> headline lever — the crypto floor + the service loop + the Microkit-PD shape) and
> (ii) the pg/Lean process-model spike (`docs/PG-DREGG.md` §11.3) re-run in the seL4
> environment. **Lever:** neither blocks the near-term path (3a) or D-sidecar; Tier
> D is the north star, gated on the executor PD becoming a service first.

### 3c. PURIST — native-seL4 Postgres via a POSIX personality

**The proposition.** No VM, no guest Linux: Postgres runs as a *native* seL4
component, its POSIX/libc expectations satisfied by a **Genode-style POSIX
personality** (a libc + runtime that maps `open`/`fork`/`mmap`/sockets onto seL4
primitives), so the Postgres process is a first-class seL4 PD directly. This is the
cleanest end-state — one fewer layer than the VMM — and the longest-horizon.

**The precedent that it is possible at all.** **nanos** is a unikernel that runs
PostgreSQL on a *minimal* kernel — the key existence proof that "Postgres on a small
kernel, no general-purpose OS" is achievable, not a category error. nanos provides a
subset of Linux features and runs a *single process* (multi-threaded), and the
nanovms project ships a **PostgreSQL patched into a single-process, multi-threaded
shape** for exactly this (`github.com/nanovms/postgres`, a v16-era patch set,
accessed 2026-06-13) — directly relevant below, because *single-process* is the
shape that sidesteps the `fork()` challenge. **Genode** runs Unix software on seL4
(among other kernels) via its libc/POSIX runtime and, for fork-using programs, its
**`noux`** runtime: per Genode's own framing, "for applications that do not rely on
fork, Noux is not needed" — they use the plain libc/pthread layer — and `noux` is
what adds `fork`/process-supervision for the programs that do (Genode docs, accessed
2026-06-13). Together they say: a native-seL4 Postgres is **research, not fantasy** —
there is a path (a single-process Postgres on a libc layer, or a fork-using Postgres
on a noux-class runtime), and pieces of it exist in other projects.

**The honest challenges (named, not waved).** Postgres's process model is the work:

- **`fork()`** — Postgres is a multi-process server: the postmaster `fork()`s a
  backend per connection (and the autovacuum/bgwriter/checkpointer/WAL-writer
  auxiliary processes). seL4 has no `fork()`; a POSIX personality must emulate it
  (spawn-a-fresh-PD-and-copy, the hard part of any seL4 POSIX layer) or Postgres
  must be reshaped toward a threaded/spawn model. This is the central challenge —
  and there are **two cited escape routes**: (i) a **noux-class** runtime that *does*
  provide `fork`/process-supervision (Genode's `noux`), hosting an unmodified
  multi-process Postgres; or (ii) the **single-process Postgres** the nanos project
  already maintains (`github.com/nanovms/postgres`), which trades the multi-process
  model for threads and so needs no `fork()` at all. The second is the lighter fit
  for a minimal kernel, at the cost of carrying a Postgres fork.
- **shared memory** — Postgres's shared buffers, lock tables, and the
  `ShmemAlloc` arena are a large System-V/POSIX shared-memory segment every backend
  maps. On seL4 this is a shared frame-cap region the personality must set up and
  hand to each backend PD — doable (it is just frame caps) but it is bespoke wiring,
  not a free `shm_open`.
- **the process model generally** — signals, process groups, the postmaster's
  `waitpid`-driven supervision, and the file-descriptor inheritance across `fork()`
  all need personality support. This is the bulk of "make a POSIX personality good
  enough for Postgres specifically."
- **mmap + a filesystem** — Postgres assumes a real filesystem and `mmap` for some
  paths; seL4 ships neither for free (`docs/SEL4-EMBEDDING.md` §3). The persist PD's
  content-addressed/block-cap storage (`docs/ROBIGALIA-ROADMAP.md` §4) is the
  substrate, but bridging Postgres's filesystem expectations onto it is part of the
  personality.

So path (3c) is **long-term research**: the safety spine holds trivially (a native
PD is confined and write-gated exactly as §1 describes — arguably *more* cleanly than
a guest, since there is no VMM in the trusted path), but the *engineering* to get
unmodified-or-lightly-forked Postgres running natively is a substantial POSIX-
personality effort. It is named here as the architectural end-state — the cleanest
embedding — explicitly gated behind paths (3a) and (3b), in the same spirit
`docs/ROBIGALIA-ROADMAP.md` §1 gates the confined-Servo renderer PD.

> **Seam (the POSIX personality):** native Postgres needs a `fork()`/shmem/process-
> model personality over seL4 (Genode-class work). **Lever:** adopt rather than
> build — Genode's libc/noux and the nanos precedent are the prior art; the
> dregg-specific work is the storage bridge (persist PD ↔ Postgres files) and the
> submit-queue/mirror IPC, which are shared with path (3a). This is the
> research-horizon item; do not claim it near.

---

## 4. The sqlite-vs-Postgres framing, concretely

ember's framing — *some OSes embed SQLite (fine); some embed Postgres (wao)* — is
not idle. SQLite is the natural thing to embed in a small OS: a single-file
in-process library, no server, modest surface. Embedding **Postgres** is a bigger
claim, and it buys things SQLite structurally cannot. Each of the following is a
capability the *Postgres* embedding gives dregg-OS that a SQLite embedding would
not — and each composes with the spine (none of them is a write path that bypasses
the executor).

### 4.1 RLS-caps — row-level security as the dregg capability gate

Postgres has **Row-Level Security**: a policy engine that filters every row of
every query by a predicate, in the database engine. SQLite has no RLS. pg-dregg
makes that engine call the *verified dregg capability decision* per row
(`docs/PG-DREGG.md` §2, §6): `USING (dregg_admits('read', id::text))` means a
reader sees only the rows its `dga1_…` credential admits — with the full capability
discipline (attenuation chains, delegation, time-boxing, caveats, third-party
discharge, revocation) SQL `USING`-predicates structurally cannot express
(`docs/PG-DREGG.md` §1). Inside dregg-OS this is the **content** capability layer
(§1.4): the seL4 caps confine the Postgres PD; the RLS-caps decide which rows flow
out of it. *The OS gets a capability-gated query engine for free* — every `SELECT`
is already dregg-authorized at the row, by the database, before a byte leaves the PD.

### 4.2 The verified write spine — submit-queue, not a mutable store

This is the safety keystone restated as a *capability*. A SQLite-embedding OS that
let the app write the database directly would have re-opened the bypass the spine
forbids. pg-dregg instead makes the only pg-originated write path an **enqueue**:
`dregg_submit_turn(signed_turn, agent)` records an intent into `dregg.submit_queue`,
RLS-gated by `WITH CHECK (dregg_admits('submit', encode(agent,'hex')))` — a role
enqueues *only* the turns its capability admits `submit` on
(`docs/PG-DREGG.md` §11.4, the landed outbox). The drainer
(`node/src/submit_queue_drainer.rs`) executes each through the one verified executor
gate. So the Postgres embedding gives dregg-OS a **first-class, RLS-gated submission
surface** — "a pg-user submits a verified turn FROM SQL" — without ever making
Postgres a writer of truth. *That* is the wao: a full SQL database as the front door,
with the verified executor still the sole writer behind it.

### 4.3 The drainer keystone, on seL4

The drainer (`node/src/submit_queue_drainer.rs`) is the piece that makes §4.2 safe,
and it is worth seeing its exact shape because it is the load-bearing mechanism of
the whole embedding. It:

1. reads `dregg.submit_queue WHERE status='pending'` (oldest first, resuming from
   pending on restart — crash-safe, exactly-once);
2. for each row, `postcard`-decodes the `SignedTurn` and runs the **same admission
   gates** the node's HTTP `/turns/submit` handler runs — signature over the turn
   hash, agent == signer's default cell, receipt-chain continuity;
3. executes it through `execute_via_producer` (#171, **the one executor gate**, the
   verified Lean producer authoritative);
4. resolves the row `executed` (with the receipt hash) or `refused` (with the
   reason) in one idempotent `UPDATE`.

On seL4 the drainer runs in the **executor PD's world** (it is node-side code that
holds the executor), reading the queue out of the confined Postgres PD over the
submit-queue IPC/transport (a virtio device for path 3a, an seL4 endpoint for a
native Postgres in 3c). **Postgres never executes** — it only records intents; the
drainer hands them to the real executor, which is free to refuse. A queued forgery
resolves to `refused` and moves no state. This is clause (b) of the spine made
mechanical: the queue is the airlock, the drainer is the gate-keeper, the executor
PD is the gate.

### 4.4 Federation-via-replication — and how its network cap is mediated

Postgres has **logical replication**: a subscriber tails a publisher's tables over
the wire. SQLite has nothing comparable. pg-dregg uses it for **federation**
(`docs/PG-DREGG.md` §15): the publisher's `dregg.turns` hash chain *is* the
replicated feed, and a subscriber **re-validates locally**
(`revalidate_replicated_chain`) — refusing a substituted/reordered/gapped stream,
with no call back to the publisher (the RootChain tooth is structural-on-the-rows,
so it survives replication bit-for-bit). So dregg-OS gets **federation-via-pg** — no
bespoke gossip — and a subscriber that *re-validates rather than trusts*.

Crucially, on seL4 the replication connection's **network cap is mediated by the net
PD** (`docs/ROBIGALIA-ROADMAP.md` §5), which solely holds the NIC cap. The Postgres
PD (or its guest, path 3a) cannot open a replication socket the net PD did not
broker — the federation link is *itself confined*. And the net PD de-envelopes /
Ed25519-checks at the boundary before anything reaches the executor, so the
distributed edge composes the same way the rest of the OS does: the wire is one PD's
sole cap, and even the federation stream is capability-mediated. This is the
seL4-native form of "federation that re-validates" — the chain tooth catches a
substituted *root*, and the net PD confines the *transport*.

### 4.5 The full query engine + the pg18-native feature set

The blunt difference: embedding Postgres gives dregg-OS a **complete relational
query engine** — joins, aggregates, window functions, recursive CTEs, a cost-based
planner, B-tree/GIN/GiST indexing — over the verified state mirror, RLS-gated, at
zero new trust (reads cannot violate a transition-function invariant,
`docs/PG-DREGG.md` §8). The explorer, analytics, and app queries are *plain SQL*
(`SELECT * FROM dregg.cells`), not bespoke RPC against a node. And because pg-dregg
targets **pg18** (`docs/PG-DREGG-PG18.md`), the embedding inherits the features that
*just landed* in the September-2025 release and that the mirror is built to use:

- **`MERGE … RETURNING old/new`** — the post-image applicator reports the exact
  balance delta in one atomic statement (`'INSERT +1000000'` / `'UPDATE -500'`), so
  conservation is assertable directly off the applicator (§7 of the pg18 doc);
- **virtual generated columns** — drift-free, zero-storage canonical projections
  (`cell_root_hex`, `balance_field`) computed on read;
- **`uuidv7()`** — the temporally-sortable submit-queue key, so the drainer reads
  the queue in arrival order by `id` alone (append-friendly, no v4 page churn);
- **`oauth`** — federated identity → pg role → dregg cap (composed, not bespoke):
  an OAuth subject's authority inside the database *is* its dregg capability, gated
  by RLS on every row (§6 of the pg18 doc);
- **data checksums on by default** — the page-integrity floor every higher
  guarantee assumes, now legible as `dregg.integrity_status`;
- **logical-replication `confl_*` counters** — the federation-divergence alarm
  (`dregg.replication_conflicts`) that composes with the chain tooth (§4.4);
- **B-tree skip scan, async I/O + `pg_aios`** — the read-heavy mirror gets faster
  large scans and one index serving two access paths, transparently.

A SQLite embedding offers none of this. The *wao* is concrete: dregg-OS embeds a
real, current, full-featured database — and keeps it entirely outside the trusted
base.

---

## 5. Honest scope + blockers

The discipline here is `docs/ROBIGALIA-ROADMAP.md`'s: say exactly where each piece
*is*, name every seam as work with a lever, and never let a labeled seam masquerade
as done. The safety spine (§1) is **real and airtight today** — it is an argument
about the architecture, and the architecture (confinement by seL4 caps + write-
gating by the executor) is exactly what the existing pieces already enforce. What is
*not* yet built is the embedding's *plumbing on seL4*; here is the honest ledger.

### 5.1 What is real today

- **The safety argument** — confinement (seL4 PDs have no ambient authority,
  `docs/ROBIGALIA-ROADMAP.md` §1) and write-gating (the executor is the sole writer;
  Postgres only enqueues, `node/src/submit_queue_drainer.rs`) are both real,
  enforced mechanisms, not aspirations. The spine holds by construction.
- **The submit-queue write loop** — landed and live on pg18: the outbox
  (`dregg_submit_turn` + the `submit_gate` RLS) and the drainer
  (`node/src/submit_queue_drainer.rs`, with a live-pg integration test draining a
  real turn to a terminal status). This is the keystone, and it exists.
- **The Tier-A/B/C mirror** — landed and live on pg18 (`docs/PG-DREGG.md` §13:
  M1/M2/M2.5 GREEN): RLS-caps, the queryable state mirror, the verified-store chain
  tooth. The whole queryable-projection surface is real *on a conventional node*.
- **The five-PD seL4 assembly** — boots (`docs/ROBIGALIA-ROADMAP.md` §1, §9): the
  executor seat, the verifier PD (a real STARK verified on-device), the persist
  stub, the net PD (a real virtio NIC brought up), the first app-PD. The PD topology
  the Postgres PD slots into *exists and boots*.
- **The VMM substrate** — the seL4 VMM (libvmm/Microkit + sDDF virtio) is a real
  seL4-Foundation framework, and `docs/ROBIGALIA-ROADMAP.md`'s net PD already uses
  virtio + sDDF-shaped rings — so path (3a)'s machinery is the same machinery the
  roadmap already runs.

### 5.2 The blockers, each with its lever

1. **The Postgres PD is not yet wired into the assembly.** No VMM-guest seat hosts
   Postgres today, and the mirror-feed + submit-queue transports across the PD/VMM
   boundary (§2.3, §4.3) are not built. **Lever:** path (3a) on the existing
   substrate — add a libvmm guest seat to the Microkit assembly (the same shape as
   the net PD) and bridge the two transports over virtio; the *projection* and
   *drain* logic already exist (the live `PgSink` + `submit_queue_drainer.rs`), only
   the transport changes from TCP to virtio.

2. **libvmm is not production-ready** (its README states it is "in-development and
   frequently changing, and is not ready for production use," accessed 2026-06-13;
   AArch64 only, RISC-V in development). **Lever:** acceptable for a confined devnet
   — the confinement argument depends on the *seL4 cap partition* being correct (the
   machine-checked part, modulo the MCS-config verification completing per §3a), not
   on the VMM being bug-free; track libvmm upstream toward production. (For a RISC-V
   target, libvmm's RISC-V support must mature first; AArch64 is the near-term VMM
   target, which matches the roadmap's primary `qemu-system-aarch64` line.)

3. **Tier-D-on-seL4 (in-process executor) is gated on the Lean-runtime port.** The
   executor-in-Postgres path (3b) cannot exist until the Lean runtime is a
   steady-state seL4 component — and that is the robigalia roadmap's own headline
   lever, currently at a one-turn heartbeat, not a service
   (`docs/ROBIGALIA-ROADMAP.md` §3). **Lever:** it rides the *same* work (crypto
   floor + service loop + Microkit-PD shape) that carries the executor PD from
   heartbeat to service; until then, path (3a) *is* the sound D-sidecar.

4. **The pg/Lean process-model hazard** (`docs/PG-DREGG.md` §11.3) applies to (3b)
   unchanged on seL4 — pg's `setjmp`/`longjmp` vs a Lean runtime mid-stack.
   **Lever:** the spike `docs/PG-DREGG.md` §13.1 decision 4 prescribes, re-run in
   the seL4 environment; D-sidecar (= path 3a) sidesteps it entirely.

5. **Native-seL4 Postgres (3c) is research.** The `fork()`/shmem/process-model
   POSIX personality is a substantial effort. **Lever:** adopt prior art (Genode's
   libc/noux, the nanos unikernel precedent that Postgres *can* run on a minimal
   kernel) rather than build from scratch; the dregg-specific glue (storage bridge,
   submit-queue IPC) is shared with (3a). This is the long-horizon end-state, named
   as research.

### 5.3 The throughline

The safety spine is the point, and it is the part that is **done as an argument**:
Postgres — all 1.5M lines of it — embeds into dregg-OS without entering the trusted
base, because the seL4 cap partition confines it and the verified executor gates its
writes. The three realization paths are a feasibility ladder from *buildable-now*
(a confined Linux-guest Postgres under the seL4 VMM, every pg-dregg feature working
unmodified) through *gated-on-the-Lean-port* (the executor in-process, atomic with
app data — the north star) to *research* (native-seL4 Postgres via a POSIX
personality). At every rung the embedding is a **queryable projection + a submission
queue**, never the trust boundary — two capability layers composing, a dregg cap
inside an seL4 cap, all the way down.

---

*dregg-OS can embed Postgres — the full pg18 query engine, RLS-caps, federation,
the verified write loop — as a confined seL4 component that never joins the trusted
base. The microkernel mediates every syscall Postgres makes (it touches only the
caps its PD holds), and the verified executor is the sole writer of authoritative
state (Postgres can only enqueue a signed turn the executor independently
validates). So a 1.5-million-line unverified C program becomes a queryable
projection and a submission surface whose worst failure is a stale read or a dropped
submission — never a forged transition. The near-term path runs unmodified Postgres
in a confined Linux guest under the seL4 VMM, on the same virtio+sDDF substrate the
robigalia roadmap already boots; the deep path links the verified executor into the
backend for cross-domain atomicity, gated on the Lean-runtime port; the purist path
runs Postgres native on seL4 via a POSIX personality, honest research with a real
precedent (nanos runs Postgres on a minimal kernel). Two capability layers compose
— the SQL RLS-caps over the seL4 caps — and that composition is the safety: a dregg
capability inside a seL4 capability, the same abstraction at two scales.*
