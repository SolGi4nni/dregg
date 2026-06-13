# Starbridge v2 — the dregg master interface

Starbridge v2 is dregg's master interface: a fully native, live, visual
environment for a verified object-capability operating system. It embeds the
real verified executor and runs a live local dregg world in-process — a single
image you can see, inspect, and drive, where every action is a verified turn.

This document explains it from first principles, present tense.

## The thesis: surpassing Smalltalk

Smalltalk gave us the *live image*: one persistent world where everything is a
live, inspectable, modifiable object, and the tools are themselves objects in
that same world. Starbridge v2 keeps that — every cell, capability, receipt, and
the image itself is a live `Inspectable` object behind one uniform interface —
and surpasses it on the four axes Smalltalk's image lacked, each made visible
and live in the cockpit:

1. **ocap security.** Objects are capability-secured cells; there is no ambient
   authority. Every action is gated by a held capability and by the target
   cell's permissions. The cockpit shows the capability graph as first-class,
   and an over-grant is *rejected by the real executor* — the no-amplification
   guarantee fires in front of you.
2. **formal verification.** Messages are verified turns carrying guarantees
   (value conservation, no capability amplification, receipt-chain integrity).
   The same verified executor that the federation runs as its authoritative
   state producer runs *here, in this process*. A turn that would violate a
   guarantee does not commit.
3. **provenance.** Every committed turn leaves a `TurnReceipt`. The receipt chain
   is a first-class, navigable causal history — the local blocklace — that you
   browse and time-travel through.
4. **distribution.** The image is a cryptographically-committed verified state
   (`state_root()`), one of a federation of sovereign images. The cockpit
   presents the image's commitment and (as the federation lane lands) its place
   among peers.

The bumper-sticker: *a live image where every object is capability-secured,
every message is a verified turn, every turn leaves a receipt, and the whole
image is a cryptographic commitment among sovereigns.*

## Two builds, one codebase

Starbridge v2 mirrors the `verifier/` `no-lean-link` pattern: one codebase, two
builds selected by feature.

### `native-full` (default) — the master interface

```
cargo build --manifest-path starbridge-v2/Cargo.toml
```

The headline build. It **embeds the real verified executor** and runs a live
local dregg world natively:

- The engine is `dregg_turn::executor::TurnExecutor` over a `dregg_cell::Ledger`
  — the exact pair the SDK's `DreggEngine` (`sdk/src/embed.rs`) wraps and that
  THE SWAP makes the federation's authoritative producer. Turns run *locally,
  in-process*; nothing is phoned to a remote node.
- This links the verified Lean archive (`libdregg_lean.a`, multi-MB). That is
  completely fine for a native desktop application — it is the very thing the
  `no-lean-link` crates exist to *avoid*, and exactly what the master interface
  *wants*.
- It renders with gpui (Zed's GPU UI framework). The whole cockpit is the
  visual layer over the embedded world.

### `sel4-thin` — the eventual seL4 component

```
cargo build --manifest-path starbridge-v2/Cargo.toml --no-default-features --features sel4-thin
```

The Lean-free, gpui-free thin path for the eventual seL4 protection-domain
component (see `docs/SEL4-EMBEDDING.md`, owned by a separate lane). It compiles
*without* the embedded executor and *without* the heavy native UI stack: it
speaks the node's HTTP+SSE wire contract (`src/client.rs` + `src/model.rs`)
against a remote node. The built binary links **zero** Lean symbols and **zero**
Metal/gpui — a clean reads-bytes → verify shape.

The `NodeClient::{Mock,Http}` wire surface is the seed of a native
remote-federation panel too (a designed-pending lane): the master interface can
*additionally* connect to remote nodes/federations, but its headline capability
is the embedded local world.

## Architecture

The headless heart is gpui-free and `cargo test`-able; the visual layer renders
it. The split:

```
starbridge_v2 (lib, feature embedded-executor)
├── world      — World: the embedded executor + live ledger + provenance log.
│               THE COMMIT PATH (`World::commit_turn`) runs the REAL executor.
├── dynamics   — Dynamics: an append-only observation stream of state
│               transitions (cell born, cap granted, turn committed, balance
│               flowed) the visual layer renders. Decoupled from gpui.
└── reflect    — the reflective object model: cell / receipt / image projected
                into one uniform `Inspectable` (typed Field tree) every view
                consumes. Reads the live protocol types — never a parallel wire
                schema — so it cannot drift from what the executor holds.

starbridge-v2 (bin)
├── cockpit    — the gpui cockpit (feature gpui-ui): the comprehensive panels
│               (cell world · inspector · blocklace · composer · dynamics),
│               rendering `World` directly.
├── views      — shared gpui palette/primitives.
├── client     — the wire-contract NodeClient (feature sel4-thin).
└── model      — the node's JSON response types, mirrored (feature sel4-thin).
```

### The commit path is the whole story

Every state transition flows through `World::commit_turn(turn)`, which:

1. threads the per-agent receipt-chain head the executor enforces,
2. runs `TurnExecutor::execute(&turn, &mut ledger)` — the real verified
   semantics,
3. on commit: records the new chain head, advances the height, appends the
   `TurnReceipt` to the provenance log, and emits the dynamics events for the
   transition,
4. on rejection: surfaces the executor's reason (this is a *feature* — it is the
   ocap/verification guarantees firing).

A rejection is not an error path to hide; it is the cockpit's most important
teaching moment. The "⚠ over-grant" verb exists precisely to make you watch the
no-amplification guarantee reject an illegitimate capability grant.

## The window (the Metal path)

gpui renders through Metal on macOS. By default its `gpui_macos` backend
compiles its shaders **at build time** with `xcrun metal` — which needs the
offline *Metal Toolchain* component. On a host whose Metal Toolchain download is
blocked or damaged (`xcodebuild -downloadComponent MetalToolchain` failing on a
broken `DVTDownloads.framework`), that build step fails and no window can open.

Starbridge v2 sidesteps this entirely by enabling gpui's **`runtime_shaders`**
feature (`gpui_platform/runtime_shaders`, wired through this crate's `gpui-ui`
feature). With it, the backend ships the `.metal` *source* and compiles it **at
runtime** via the system Metal framework (`MTLDevice::newLibraryWithSource`) —
no offline toolchain involved. This is the difference between a window that
opens and a build that fails, and it is load-bearing on exactly the kind of host
the prior scaffold stalled on. The window opens; the embedded `Metal.framework`
device is live; runtime shader compilation succeeds.

A `--headless` flag runs the embedded world's self-check (cells, provenance
chain, dynamics) with no window — CI-friendly, and the graceful fallback on a
host with no display.

## Comprehensive coverage — all data & all actions

The master interface is, by design and increasingly by implementation, a cover
over EVERY dregg datum and EVERY action. The coverage is an honest burn-down:

### Data

| Datum | Status | Where |
| --- | --- | --- |
| cells (id/balance/nonce/caps/program/delegate/mode/lifecycle/epoch) | **live** | `reflect::reflect_cell` |
| cell state fields (16 slots) | **live** | inspector `state[i]` rows |
| capabilities + the ocap edges | **live** | `CapEdge` fields per cap |
| receipts + the receipt chain (provenance) | **live** | `reflect::reflect_receipt`, blocklace panel |
| the image commitment (`state_root`) | **live** | `reflect::reflect_image` |
| the dynamics stream (transitions) | **live** | `dynamics`, the feed |
| capability delegation *graph* (multi-hop layout) | designed-pending | edges present per-cell; a whole-graph view is next |
| full delegation epochs / revocation channels | partial | epoch shown; channel view pending |
| organs (trustline/channel/mailbox/court) state | designed-pending | mirrored types catalogued; panels pending |
| intents / factories / obligations / nullifiers | designed-pending | node API mapped; panels pending |
| proofs + verification status (STARK) | designed-pending | executor runs full semantics; proof-attach view pending |
| profiles / identities, producer lean-vs-rust | partial (thin path) | surfaced in the thin client; native badge pending |
| federations + sync state | designed-pending | `state_root` is the local half; peer view pending |

### Actions (verbs)

| Verb | Status | Where |
| --- | --- | --- |
| transfer | **live** (runs the real executor) | `world::transfer`, composer |
| grant capability | **live** | `world::grant_capability`, composer |
| over-grant (rejected) | **live** (guarantee fires) | composer "⚠ over-grant" |
| createCell (conservation-enforced) | **live** | `world::create_cell` |
| set state field | **live** | `world::set_field` |
| emit event | **live** | `world::emit_event` |
| revoke capability | wired (helper) | `world::revoke_capability` |
| seal / unseal / destroy / burn | designed-pending | `Effect` variants reachable via `World::turn` |
| factory-birth | designed-pending | `Effect::CreateCellFromFactory` path |
| the organ operations (open/draw/repay; create/join/remove; send/drain; evidence) | designed-pending | SDK organ surfaces catalogued |
| compose+sign+submit (multi-action call forests) | partial | single-action turns live; multi-action composer next |
| connect to federations | designed-pending | `NodeClient::Http` exists; native panel pending |

The "live" rows all run through the embedded verified executor with real
receipts; the "designed-pending" rows are reachable through the same
`World::turn` / `commit_turn` path (every `Effect` variant is constructible) and
are a UI/affordance burn-down, not a semantics gap.

## Tests

The headless heart is fully `cargo test`-able under just `embedded-executor`
(no gpui, no window):

```
cargo test --manifest-path starbridge-v2/Cargo.toml --no-default-features --features embedded-executor --lib
```

16 tests cover: transfer commits + conserves; **overspend rejected**; **over-grant
rejected** (no-amplification); legitimate grant grows the ocap graph; createCell
grows the ledger under conservation; setField writes state; emit-event commits;
the receipt chain links across turns; the image commitment moves with history;
the dynamics stream observes transitions; the reflective model projects cells,
receipts, and the image; and the demo world boots with real provenance.

## Status

GREEN on the thesis "the master interface is real and growing": the embedded
verified executor runs a live local world, the four axes are all live in the
engine, the headless heart is tested green, both builds compile, the
`sel4-thin` binary is confirmed Lean-free + Metal-free, and **the gpui window
opens** (runtime shaders defeat the missing Metal Toolchain). The breadth of
"comprehensive for ALL data & actions" is the active burn-down above.
