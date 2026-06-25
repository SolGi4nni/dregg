# dregg / deos — what it is

A light client holding one root knows every transition in the whole history was
authorized, conservative, fresh, and correctly committed — re-executing nothing.

That sentence is the system. Everything below is how it is true.

## The model — four words

- **Cell** — the unit of state and identity. A cell holds four substances: *value*
  (per-asset signed balances), *state* (programmable slots + a nonce), *authority* (a
  capability tree), *evidence* (append-only nullifier / commitment / epoch ledgers). A
  card, a document, an agent, a room, a service, you — each is a cell.
  (`cell/src/cell.rs`, `cell/src/state.rs`.)
- **Capability** — a directed edge: "this cell can produce a witness the kernel accepts
  for authority over that one," carrying attenuated rights. You *hold* a capability iff
  you can *produce* its witness — never merely be named in a table. Authority is
  production under non-forgeability, not possession of a key.
- **Turn** — one authorized inference step: a forest of actions, executed as a
  transaction (all-or-nothing, journalled), each action gated by the kernel before it
  commits. (`turn/src/`, executor under `turn/src/executor/`.)
- **Receipt** — a turn's verifiable witness. It binds the whole post-state: tampering a
  field the effect did not legitimately write makes the turn unprovable (the anti-ghost
  property).

## The map

- **The verified kernel** — Lean (`metatheory/Dregg2/`) defines cells, the four
  substances, the verbs, the executor, and proves the guarantees a light client relies
  on. Authority = production under non-forgeability; conservation = Σδ=0; the apex is
  light-client unfoolability. See [`KERNEL.md`](KERNEL.md). The skeptic-facing ledger of
  exactly what is proved (and what is not) is `metatheory/CLAIMS.md`; the conceptual
  spine is `metatheory/CONSTRUCTIVE-KNOWLEDGE.md`.
- **The descriptor circuit & light client** — each turn carries a STARK proving it was a
  valid kernel transition. A light client holds no secrets, re-runs no cell, and yet —
  checking only a succinct root — learns the whole history is genuine
  (`metatheory/Dregg2/Circuit/`, `circuit/`, `sdk/`).
- **deos / the desktop** — a workspace where every action constructs a verifiable fact
  and adds zero new trust: an affordance is a cap-gated turn template, login is the root
  capability, history is the receipt chain, sharing is a cap-confined membrane. The
  interface is direct manipulation of the kernel's own semantics — see
  [`deos/HIG.md`](deos/HIG.md) (the interface spine) and `docs/deos/` (the vision set:
  `DEOS.md`, `COCKPIT-UX.md`, `HYPERDREGGMEDIA.md`).
- **The realization** — the running system: `cell/`, `turn/`, `circuit/`, `sdk/`, the
  node, and `starbridge-v2` (the cockpit). The `@[export]` C-ABI entries
  (`metatheory/Dregg2/Exec/DistributedExports.lean`) let the Rust runtime compute its
  verdict *from* the verified Lean.

## Where to go next

- To run a node, log an agent in, or drive the self-hosting loop: the runnable how-tos
  in `docs/deos/` (`DEV-NODE-RUNBOOK.md`, `LOG-A-HERMES-IN.md`, `SELF-HOSTING-LOOP.md`).
- To use or develop against the system: `docs/MANUAL/` (`USER.md`, `DEVELOPER.md`).
- For the exact proof inventory and honesty labels: `metatheory/CLAIMS.md`.
