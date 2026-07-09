# starbridge-branch-stitch-multiplayer

**The distributed-Houyhnhnm flagship, runnable — two participants fork ONE shared verified
world, diverge on independent verified branches, and stitch back through a single
settlement-sound gate.**

`ada` and `boris` co-inhabit a shared `World`, each fork it, drive real verified turns on
their own branch, and rejoin. The stitch is not a merge heuristic — it is the proven
`settlement_soundness` gate, live: disjoint edits fold clean, a clash is refused fail-closed,
and a capability revoked on main between branch and settlement cannot ride the rejoin.

Unlike the other starbridge-apps this crate ships **no `FactoryDescriptor` / `CellProgram` of
its own** and installs no slot caveats. It is a `[[bin]]` (`src/main.rs`, no `lib.rs`) that
composes [`starbridge_v2::branch_stitch_session::BranchStitchSession`] — the transport-free
primitive lifted from `ForkMembraneHost::stitch_pair` — over `embedded-executor` only. So it
doubles as a runnable narration AND an integration test of the settlement-sound branch-and-stitch.
It is the first app to depend on `starbridge-v2` with `embedded-executor` alone: no GPU, no
Matrix, no cockpit transport.

```
cargo run -p starbridge-branch-stitch-multiplayer   # gpui-free, no GPU
```

## The three beats (each a real fork → verified turns → settlement)

The property being enforced is **settlement soundness** — the stitch admits exactly what a
capability-secure, conservation-preserving rejoin may admit, and nothing else. Each beat
asserts it internally (`src/main.rs`), and the whole arc is an acceptance test.

| Beat | Setup | What the gate does | Where |
|---|---|---|---|
| **A · disjoint MERGE** | `ada` and `boris` edit non-overlapping addresses | both branches' writes fold into the settled root; conservation + authority preserved; **main stays pristine** (divergence is reversible/imaginary until applied) | `beat_a`, `src/main.rs:93` |
| **B · clash REFUSED** | both write the SAME address (`board.field[0]`) | the stitch **does not settle** — `state_conflicts` names the exact diverged address, both attributed readings kept; **never a silent last-writer-wins** | `beat_b`, `src/main.rs:156` |
| **C · revoked cap LINEAR-DROPPED** | a `gift` cap is revoked on MAIN between branch and settlement | the same stitch **drops** `gift` from `admitted_authority` into `dropped_authority` while the disjoint state **still settles** (the drop is orthogonal to the pushout) | `beat_c`, `src/main.rs:188` |

Beat C is proven **non-vacuous both ways**: before the revoke, `gift` is held at the tip and
*rides* the stitch (`admitted_authority`); the revocation is a real verified turn on main; only
*after* it does the drop appear (`before.dropped_authority != after.dropped_authority`,
`src/main.rs:272`). The drop IS the revocation — not a blanket refusal.

## What it composes (no bespoke engine)

- `BranchStitchSession::open / fork / drive / stitch / base` — the branch-and-stitch primitive.
- `World`, `make_open_cell`, `set_field`, `revoke_capability` — from `starbridge_v2::world`;
  every branch edit is an ordinary cap-gated verified turn, and the beat-C revoke is one too.
- A `Cast` of ordinary cap-gated genesis cells (a `room` focus reaching both principals + a
  shared `board`, each principal's own doc, a conferrable `gift` cap, and an `offstage` cell
  granted to nobody — the confinement foil that must never ride the cap-bounded cull).

## Honest limits

This is the transport-free slice (`docs/deos/BRANCH-AND-STITCH-APP-PLAN.md`, slice 0). It runs
the settlement-sound primitive over an in-process `embedded-executor` — there is no network
membrane, no cockpit UI, and no service/card surface. It exercises exactly two participants and
the three canonical beats; it is a demonstration and an integration test, not a general
multi-party collaboration server.

## Run

```
cargo run  -p starbridge-branch-stitch-multiplayer   # print the three-beat arc
cargo test -p starbridge-branch-stitch-multiplayer   # the arc as an acceptance test
```
