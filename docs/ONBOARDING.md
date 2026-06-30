# ONBOARDING — orient fast

You are a new Claude session, a new human, or a new agent. Read **this one doc**
and you will know the shape: what dregg is, the repo layout, and the exact "read
these first" path into the depth. Everything here is grounded to the real current
state — it does not aspirational-ize. Where something is staged, partial, or
single-token-gated, it says so.

The one-sentence through-line: **dregg is the verified, open substrate that says
what was promised, paid, and owed — verifiably.**

---

## 1. What dregg is

dregg ("Dragon's Egg") is a **formally verified, distributed object-capability
operating system**. The kernel is a Lean 4 program with machine-checked
soundness, and it is the *exact* function the running node executes. Every state
transition is gated by an unforgeable capability, leaves a verifiable receipt,
and carries a STARK proof a light client can check without re-running history.

The whole system in one sentence: *a light client holding one root knows every
transition in the whole history was authorized, conservative, fresh, and
correctly committed — re-executing nothing.*

The four words of the model ([`docs/OVERVIEW.md`](OVERVIEW.md)):

- **Cell** — the unit of state and identity. Holds four substances: *value*
  (per-asset balances), *state* (slots + nonce), *authority* (a capability
  tree), *evidence* (append-only ledgers). A card, a document, an agent, a room,
  a service, you — each is a cell.
- **Capability** — a directed edge carrying attenuated rights. You *hold* a
  capability iff you can *produce* its witness — never merely be named in a
  table. Authority is production under non-forgeability, not possession of a key.
- **Turn** — one authorized inference step: a forest of actions executed as a
  journalled transaction, each action gated by the kernel before it commits.
- **Receipt** — a turn's verifiable witness; it binds the whole post-state, so
  tampering a field the effect did not legitimately write makes the turn
  unprovable (the anti-ghost property).

On top of the kernel, **deos** is the agentic desktop userlayer — the same
proofs made visual: a window *is* a capability, an interaction *is* a verified
turn. (Naming: **robigalia** the project · **dregg** the kernel · **deos** the
desktop. *deos runs on dregg runs in robigalia.*)

### Read these first (dregg depth, in order)

1. [`docs/OVERVIEW.md`](OVERVIEW.md) — the four-word model + the map. Start here.
2. [`docs/atlas/atlas.html`](atlas/atlas.html) — the visual atlas of the whole
   system (open it in a browser). The fastest way to *see* the shape.
3. [`metatheory/CONSTRUCTIVE-KNOWLEDGE.md`](../metatheory/CONSTRUCTIVE-KNOWLEDGE.md)
   — the conceptual spine: why a capability *is* constructive knowledge.
4. [`metatheory/docs/DREGG-CALCULUS.md`](../metatheory/docs/DREGG-CALCULUS.md) —
   the calculus the kernel is built on.
5. [`docs/KERNEL.md`](KERNEL.md) — the verified kernel: the verbs, the executor,
   the guarantees. The skeptic-facing proof ledger is
   [`metatheory/CLAIMS.md`](../metatheory/CLAIMS.md) (what is proved, what is not).
6. [`docs/reference/`](reference/) — the **grounded what-is** for every
   subsystem, each pinned to `file:line` at HEAD. When a memory/summary and a
   reference doc disagree, **the reference wins**.

### If you want to *use* or *build*, not just understand

- [`QUICKSTART.md`](../QUICKSTART.md) — 15 minutes: a node running + a real turn
  signed on `localhost`.
- [`docs/guide/`](guide/) — the developer onramp (build-with-dregg, what you can
  build, deos-from-the-web, the agent quickstart for LLMs).
- [`docs/MANUAL/`](MANUAL/) — the author's user + developer manuals.
- The SDKs: `sdk/` (Rust core), `sdk-py/` (Python), `sdk-ts/` (TypeScript).

---

## 2. The repo

| | what it is | license | where |
|---|---|---|---|
| **dregg** (breadstuffs) | the verified ocap substrate — kernel, value layer, intent ring, Payable, the execution-lease (the on-substrate, light-client-witnessed record of a workload + metering + payment) | **AGPL-3.0, public** | `~/dev/breadstuffs` |

---

## 3. The orient path in one glance

```
   ┌─ you are here: ONBOARDING.md ─┐

   want the SUBSTRATE?
   OVERVIEW.md → atlas.html →
   CONSTRUCTIVE-KNOWLEDGE.md →
   KERNEL.md → reference/

   want to BUILD?
   QUICKSTART.md → guide/ → MANUAL/
```

For a fresh Claude session specifically: orient from the durable record
(`REORIENT.md` → `HORIZONLOG.md` → the memory index), read for the *shape*, then
**verify code vs HEAD for the state** — memories are dated and point-in-time, and
`docs/reference/` (grounded to `file:line`) is the source of truth for what each
subsystem *is*.

---

*Honest-state footnote: the Solana bridge is devnet/oracle today; the
house-capacity circuit welds are partly staged (the executor tooth is real today,
the light-client circuit tooth is its named shadow — see the memory index).
Verify against HEAD.*
