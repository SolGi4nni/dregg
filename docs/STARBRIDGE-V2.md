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
cd starbridge-v2 && cargo build
```

Build *from inside* `starbridge-v2/` — not `--manifest-path` from the repo root.
`rust-toolchain.toml` is directory-scoped: this crate pins the rolling `nightly`
because gpui needs `std::hint::cold_path`, which stabilized after the repo root's
`nightly-2026-01-01`. Building from the root selects that older toolchain and
fails to compile gpui with E0658 (`cold_path` unstable). If the rolling nightly
is itself stale, `rustup update nightly` refreshes it — this affects only this
standalone crate (the root + every other lane pin a dated nightly).

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
cd starbridge-v2 && cargo build --no-default-features --features sel4-thin
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
│               (cell world · inspector · blocklace · composer · objects ·
│               dynamics) plus the workspace tabs (composer · objects · debugger
│               · replay · cipherclerk · editor), rendering `World` directly. The
│               OBJECTS tab projects proofs / nullifiers / cell lifecycle through
│               `reflect`. A ⌘K COMMAND PALETTE (`palette`) overlays the whole
│               cockpit: one fuzzy-searchable surface over EVERY action.
└── palette    — the ⌘K command registry + fuzzy matcher + selection model
                (gpui-free, testable). Every cockpit action is one `CommandId`;
                the cockpit dispatches a selected command through the SAME
                `&mut Cockpit` verb the buttons call — no parallel action path.
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
| cell lifecycle (live / sealed / destroyed / migrated / archived) | **live** | OBJECTS panel lifecycle column, `lifecycle_badge` |
| proofs + verification status (STARK) | **live** | `reflect::reflect_proof_status`, OBJECTS panel |
| nullifiers / consumed one-time authorities | **live** | `reflect::reflect_nullifiers`, OBJECTS panel |
| factories (deployed descriptors) | **live** | `reflect::reflect_factory`; deploy + birth path |
| capability delegation *graph* (multi-hop layout) | designed-pending | edges present per-cell; a whole-graph view is next |
| full delegation epochs / revocation channels | partial | epoch shown; channel view pending |
| organs (trustline/channel/mailbox/court) state | designed-pending | trustline/flashwell in embed-core; channel/mailbox need `captp` (network), surfaced as remote-path |
| intents / obligations | designed-pending | node API mapped; panels pending |
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
| seal / unseal | **live** (runs the real executor) | `world::seal` / `world::unseal`, composer "seal a fresh cell" |
| destroy (terminal retirement) | **live** | `world::destroy`, headless test |
| burn (supply reduced, `was_burn` bound) | **live** | `world::burn`, composer "burn 1,000" |
| factory-birth (`CreateCellFromFactory`) | **live** | `world::deploy_factory` + `world::create_cell_from_factory` |
| compose multi-action call forests | **live** | `world::forest_turn` (atomic, one receipt), composer "compose multi-action" |
| the organ operations (open/draw/repay; create/join/remove; send/drain; evidence) | designed-pending | trustline/flashwell organ surfaces in embed-core; channel/mailbox/court need `captp` (remote path) |
| connect to federations | designed-pending | `NodeClient::Http` exists; native panel pending |

> **Lifecycle finding — seal/destroy are recorded, the *verbs* enforce
> terminality, but ordinary effects are not yet gated.** The verified executor
> records the `Sealed` / `Destroyed` lifecycle, and the lifecycle verbs
> themselves enforce their own invariants (unseal of a live cell rejects;
> double-destroy rejects; over-burn rejects). But the executor's apply path does
> not yet consult `CellLifecycle::accepts_effects()` before *non-lifecycle*
> effects, so a sealed/destroyed cell does not currently freeze ordinary effects.
> The cockpit surfaces the lifecycle state honestly (the OBJECTS lifecycle
> column); wiring the effect-freeze gate is an executor lane, not the
> interface's to fake.

The "live" rows all run through the embedded verified executor with real
receipts; the "designed-pending" rows are reachable through the same
`World::turn` / `commit_turn` path (every `Effect` variant is constructible) and
are a UI/affordance burn-down, not a semantics gap.

### The developer experience: cipherclerk + ⌘K (live)

Two DX surfaces are first-class and wired to the real engine, not read-only
demos:

**The cipherclerk surface — real macaroon mint · attenuate · delegate ·
discharge.** The CIPHERCLERK tab drives the REAL `dregg_sdk::AgentCipherclerk`
(no reimplemented crypto) through an action layer (`cipherclerk` module):
`mint` forges a root macaroon on the holder's clerk; `attenuate` confines it
(the narrowing is genuine — the attenuated token carries strictly more caveats);
`delegate` produces a real signed, recipient-targeted `DelegatedToken` envelope
and files it; `discharge` runs the real verify verdict (HMAC chain + caveat
evaluation). Two **real-semantics findings** surfaced and are honored by the
surface:

  1. *The macaroon action vocabulary is the atomic letters `r`/`w`/`c`/`d`/`C`*,
     not English words. `dregg_macaroon::action::Action::parse` decomposes a
     request action into those flags and requires EACH to be allowed — so a
     `"read"`-the-word request parses to `{r,d}` and an `r`-only token DENIES it.
     The discharge surface speaks the atomic letters.
  2. *An attenuated `HeldToken` carries a ZEROED root key* (it dropped the
     forging key), so the **holder cannot self-`verify_token`** a confined token
     — only the **verifying service**, which holds the root key, can discharge
     it. The surface exposes both: a holder-side self-check (`discharge`) for a
     root token, and a service-side `discharge_presented(token, root_key, req)`
     for a presented confined token.

**The ⌘K command palette — one searchable surface over ALL actions.** Press ⌘K
(or Ctrl-K) to open a centered, fuzzy-filtered palette over EVERY action in the
cockpit: the composer verbs, the cipherclerk loop, the workspace navigation, the
replay scrubber (step/genesis/head/fork/clear), the debugger retarget, and the
inspector. The palette is honestly comprehensive because a palette command
carries only a stable `CommandId` that the cockpit dispatches through *the exact
same `&mut Cockpit` method the buttons call* — there is no second action path,
so the palette can never drift from what the cockpit can do.

## Tests

The headless heart is fully `cargo test`-able under just `embedded-executor`
(no gpui, no window):

```
cd starbridge-v2 && cargo test --release --no-default-features --features embedded-executor --lib
```

> **Run the suite in `--release`.** The tests exercise the embedded VERIFIED
> executor (the linked Lean archive) and the cipherclerk's real macaroon HMAC /
> caveat crypto. In a debug build those paths are pathologically slow and pin the
> CPU; `--release` makes the suite run in seconds. (Plain `cargo test` without
> `--release` is correct but unbearably slow — prefer release for any iteration.)

The headless tests (green) cover: transfer commits + conserves; **overspend
rejected**; **over-grant rejected** (no-amplification); legitimate grant grows
the ocap graph; createCell grows the ledger under conservation; setField writes
state; emit-event commits; the receipt chain links across turns; the image
commitment moves with history; the dynamics stream observes transitions; the
reflective model projects cells, receipts, the image, **proof/STARK status,
factories, and nullifiers**; the demo world boots with real provenance;
**seal/unseal round-trip the lifecycle, destroy retires a cell terminally, burn
reduces supply (and over-burn rejects), factory-birth installs a child through
the registry (and an unregistered factory rejects), and a multi-action
call-forest commits atomically (all-or-nothing)**.

The DX surfaces are tested too: the **cipherclerk action layer** (mint forges a
real root; attenuate genuinely narrows; delegate files a real recipient
envelope; **discharge runs the real verify verdict** — a service-confined token
authorizes its own service/action and DENIES a wider action, a different
service, or an expired request; the full mint→attenuate→delegate→discharge loop)
and the **⌘K palette** (the registry covers the whole action surface; the fuzzy
matcher prefers word-starts + contiguous runs; search finds commands by title
AND by keyword concept; the open/type/select/accept interaction model).

## Status

GREEN on the thesis "the master interface is real and growing": the embedded
verified executor runs a live local world, the four axes are all live in the
engine, the headless heart is tested green (67 tests), the native-full build
compiles (gpui included — built from inside the crate on the rolling nightly),
and the headless self-check boots the live image. The coverage matrix above has
moved a full column to **live**: every kernel lifecycle verb (seal/unseal/
destroy/burn), factory-birth, and multi-action call-forests now run through the
embedded executor with real receipts, and the OBJECTS panel reflects proofs,
nullifiers, and cell lifecycle. The remaining **designed-pending** rows (organ
node-services behind `captp`, the multi-hop delegation graph view, intents/
obligations panels, the live federation connect panel) are the active burn-down.
