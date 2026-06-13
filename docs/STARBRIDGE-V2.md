# Starbridge v2 — the native (gpui) dregg shell

*Design + scaffold doc. Status: scaffolded crate + this design. Cites the tree
as of 2026-06-13. The honest scope split (what runs vs what is a full app's
work) is §6.*

## 0. What this is

Starbridge v2 is a **native ocap shell** for dregg, built on **gpui** (Zed's
GPU-accelerated Rust UI framework). It is the desktop sibling of the web
Starbridge shell (`site/src/starbridge/index.html`): the one persistent frame
you boot into that shows who you are, your cells, the node's receipt stream,
and lets you drive turns. The native version exists because the end state is an
**seL4 component** — a dregg shell that renders to a framebuffer capability and
talks to the node protection domain over an seL4 channel (`docs/SEL4-EMBEDDING.md`).
A browser shell cannot be that; a `no_std`-trending native Rust GUI can.

It is a **client**. It speaks the dregg node's HTTP+SSE wire contract
(`node/src/api.rs` routes, `node/src/events.rs` SSE stream). It does **not**
link the executor or the verified Lean archive (`libdregg_lean.a`). The
verified semantics run in the node it connects to; the shell renders that
node's state and composes turns to send it.

## 1. The crate is a STANDALONE workspace

`starbridge-v2/Cargo.toml` declares its own `[workspace]` and is **excluded**
from the main `/Cargo.toml` members — the same posture as `wasm/` and
`sdk-py/`, and for the same reason. gpui drags a very heavy native dependency
tree: a windowing/event-loop layer, GPU backends (Metal on macOS, Vulkan/wgpu
elsewhere), font shaping (cosmic-text/harfbuzz), `objc`/`core-foundation` on
macOS. Pulling that into the main workspace would:

- balloon every `cargo check --workspace` (the cost the `wasm` eviction commit
  `55318b702` and the root Cargo.toml comments are explicitly fighting), and
- risk feature-unification onto the Lean-linked crates — exactly the footgun
  the root Cargo.toml documents around `no-lean-link`.

So Starbridge v2 builds via its own manifest path, never feature-unifying onto
the protocol crates:

```
cargo build  --manifest-path starbridge-v2/Cargo.toml
cargo run    --manifest-path starbridge-v2/Cargo.toml -- http://127.0.0.1:8080
```

gpui is pinned to a zed commit (`rev = fca2ccd…`) because the crate is
published from the zed monorepo, not crates.io.

### Build state (honest)

**All Rust compiles** — our crate AND the entire gpui dependency tree (62
crates: gpui, font-kit, the `objc2`/`block2`/AppKit stack, reqwest, etc.). The
build stops at exactly one non-Rust step: `gpui_macos`'s `build.rs` compiles
Metal shaders (`shaders.metal`) and the host's **Metal Toolchain component is
not installed** (`cannot execute tool 'metal' … use: xcodebuild
-downloadComponent MetalToolchain`). On this machine that download is itself
blocked by a damaged Xcode `DVTDownloads` framework — a pre-existing host
provisioning problem, not a defect in this crate. Zero errors are attributed to
`starbridge-v2`. A runnable hello-window is one `xcodebuild -downloadComponent
MetalToolchain` (on a healthy Xcode) away.

Getting the gpui-from-git tree to compile under this repo required three
mechanical fixes, all documented at their site:

1. **`[patch.crates-io]` for `async-process` / `async-task`** (Cargo.toml) —
   gpui's `util` crate calls `smol::process::Child::adopt_raw_pid`, which exists
   only in zed's forked `async-process`. Consumers of gpui-from-git must
   replicate the relevant subset of zed's root `[patch]` table.
2. **Vendored `pathfinder_simd`** (`vendor/pathfinder_simd/`) — the upstream
   0.5.6 sets a `pf_rustc_nightly` cfg that selects an aarch64 SIMD module using
   portable-SIMD intrinsics that churn across nightlies. The vendor's `build.rs`
   simply doesn't set that cfg, forcing the portable scalar path (a perf trade,
   correct either way).
3. **A local `rust-toolchain.toml` pinning the rolling `nightly`** — gpui at
   this rev uses `std::hint::cold_path` (stabilized in nightly after the repo's
   `nightly-2026-01-01` pin). This crate is a standalone workspace, so the
   override touches no protocol crate.

### Why mirror the wire types instead of linking `dregg-sdk`

`dregg-sdk` on native links `dregg-lean-ffi` **unconditionally** (it is THE
SWAP producer path; see `sdk/Cargo.toml` lines 18–24). Linking the SDK would
chain the gpui build to the Lean archive build — a heavy, slow coupling that a
*rendering shell* does not need. The shell's contract with the node is a
**protocol** (JSON over HTTP/SSE), not a code dependency. So `src/model/`
hand-mirrors the node's response structs (`api::StatusResponse`,
`CellListEntry`, `CellDetailResponse`, `ReceiptInfo`, `FederationInfo`,
`SubmitTurnRequest`/`TurnActionSpec`/`TurnEffectSpec`, and `events::ReceiptEvent`).
When local-custody turn *signing* lands (build-out lane), the SDK's
turn-builder surface can be linked behind a feature — but the read/inspect/SSE
shell never needs it.

> Single-sourcing the wire contract (a shared `dregg-wire-types` crate the node
> and this shell both depend on) is the right eventual move; the hand-mirror is
> the honest scaffold until then. The invariant is noted in `src/model/mod.rs`.

## 2. Architecture — a native ocap shell

```
┌──────────────────────────────────────────────────────────────────────┐
│ Starbridge (root view, src/main.rs)                                    │
│ ┌──────────────┐  ┌──────────────────────┐  ┌───────────────────────┐ │
│ │ rail header  │  │ ReceiptInspector     │  │ TurnComposer          │ │
│ │  node status │  │  receipt stream (SSE)│  │  build actions/effects│ │
│ │  lean/rust   │  │  + per-receipt proof │  │  → SubmitTurnRequest  │ │
│ │  producer    │  │    /finality inspect │  │  → node.submit_turn() │ │
│ │ ┌──────────┐ │  └──────────────────────┘  └───────────────────────┘ │
│ │ │ CellList │ │                                                       │
│ │ │ your     │ │           NodeClient (src/client.rs)                  │
│ │ │ cells    │ │      Mock (fixtures)  |  Http { base_url }            │
│ │ └──────────┘ │              │                  │                     │
│ └──────────────┘              ▼                  ▼                     │
│                       in-process data     a real dregg node           │
│                                            (api.rs + SSE)              │
└──────────────────────────────────────────────────────────────────────┘
```

The layout mirrors the web shell: a **left rail** (identity/node + your cells)
and a **main split** (the receipt inspector + the turn composer). Each core
view is a real gpui `Render` component holding a real data model from
`src/model/`, bound to a `NodeClient`. The views never know whether they are
backed by the mock or a live node — both return the same model types.

### The three core views

| View | File | Mirrors | Drives |
|---|---|---|---|
| **CellList** | `src/views/cell_list.rs` | web rail "your cells" + `/api/cells` | the cell browser; signed balances (issuer wells carry −supply), nonce, cap count, program/delegate badges |
| **ReceiptInspector** | `src/views/receipt_inspector.rs` | web "receipt stream" (SSE) + workbench receipt inspector | the receipt list + per-receipt proof/finality/witness drill-in |
| **TurnComposer** | `src/views/turn_composer.rs` | the "drive turns through the organs" surface | builds a `SubmitTurnRequest` (thin-client effects) + submits via `node.submit_turn()` |

### The node client

`NodeClient` (`src/client.rs`) is one enum with two backends:

- **`Mock`** — in-process fixtures (`client::mock`) so the shell renders a
  populated window with no running node. This is the scaffold's default.
- **`Http { base_url }`** — blocking JSON reads against the real routes
  (`/status`, `/api/cells`, `/api/receipts`, `/api/federations`,
  `/api/blocklace/blocks`) and a `POST /turn/submit`.

Both yield `src/model` types, so wiring a live node is "pass a URL", not a
view rewrite.

## 3. Driving turns through the organs

The brief calls for driving turns "through the organs (trustline / channel /
mailbox)". The scaffold lands the **thin-client effect set** — the
JSON-friendly `TurnEffectSpec` the node already accepts on `/turn/submit`
(`SetField` / `Transfer` / `EmitEvent` / `IncrementNonce`). This is enough to
prove the composition → wire → submit loop end to end against a node.

The richer organ flows (trustline open/extend/settle, channel epoch lifts,
mailbox crank) ride the node's **typed signed-envelope** path (`/turns/submit`)
and the SDK's organ builders (`sdk/src/{trustline,channels,mailbox}.rs`). The
composer is structured so an organ flow is "another composer tab + another
request builder", not a rewrite — but each needs local-custody signing (§5) to
author the envelope, which is the gating build-out lane.

## 4. The receipt + proof inspector

The ReceiptInspector renders each committed turn's summary (chain index, turn
hash, finality, effect kinds, touched cells) and a drill-in face showing the
proof state: `has_proof`, finality, witness count. This is the honest surface
of the SWAP — a node running the legacy Rust producer is *visibly* not running
the verified semantics (the rail header shows `lean producer` green vs `rust
producer` amber), and a receipt without an attached STARK shows `pending` not
`proven`. The full proof artifact view (rendering a `FullTurnProof` /
`AttestedHistory` light-client verdict) is a build-out lane that links the
`dregg-lightclient` verifier.

## 5. The seL4-component end state

The far target (per `docs/SEL4-EMBEDDING.md`): Starbridge v2 is an seL4
**protection domain** that renders to a **framebuffer capability** and talks to
the node PD over an **seL4 channel** instead of HTTP. The capability discipline
is the point — the shell PD holds only the caps it needs (the framebuffer, the
node channel, input), and cannot touch the node's storage or executor.

What that requires of this crate:

1. **A framebuffer backend for gpui.** gpui abstracts its platform behind a
   renderer + windowing layer (Metal/wgpu today). An seL4 deployment needs a
   gpui backend that targets a raw framebuffer cap (a software or Vulkan-on-seL4
   rasterizer) and an input source over the seL4 channel rather than a desktop
   event loop. This is the hard, specialist line item — analogous to (and
   independent of) the Lean-runtime port that `SEL4-EMBEDDING.md` §2 names as
   the node-side blocker.
2. **A channel transport for `NodeClient`.** The `Http` backend becomes a
   `Channel { ipc cap }` backend speaking the same request/response contract
   over an seL4 endpoint instead of TCP. Because `NodeClient` is already a
   backend enum returning model types, this is an additive variant.

Neither is in the scaffold; both are named lanes below.

## 6. Honest scope — scaffolded vs a full app's work

**Scaffolded (real gpui, real dregg wire types, builds + runs):**

- A standalone gpui crate that opens a window and lays out the shell (rail +
  main split) mirroring the web Starbridge model.
- Three real `Render` views (CellList, ReceiptInspector, TurnComposer) bound to
  real wire-contract data models.
- A `NodeClient` with a mock backend (populated fixtures) and an HTTP backend
  wired to the real node routes.
- A turn-composition → wire-request → submit loop over the thin-client effect
  set.
- Honest SWAP surfacing (lean vs rust producer; proven vs pending receipts).

**A full app's work (NOT in the scaffold — the build-out lanes):**

- **Live SSE receipt stream.** The inspector shows a *snapshot*
  (`/api/receipts`); the live `/api/events/stream` push (driven on gpui's async
  executor, feeding `cx.notify()`) is not wired. The mock/HTTP read methods are
  blocking; live reads should move to `cx.spawn` + gpui's `BackgroundExecutor`.
- **Local-custody turn signing.** The composer submits via the node operator's
  cipherclerk (`/turn/submit`). Authoring *signed envelopes* (the `/turns/submit`
  path, and every organ flow) needs the SDK's signing surface linked behind a
  feature + a local keystore — the gating lane for the organ flows.
- **The organ flows themselves** (trustline / channel / mailbox composer tabs).
- **The full proof artifact view** (`FullTurnProof` / `AttestedHistory`
  light-client verdict rendering, linking `dregg-lightclient`).
- **Cell selection wiring across views** (select a cell in CellList → scope the
  inspector + composer to it).
- **Interaction** (buttons/inputs are rendered; gpui action handlers and text
  input fields for editing the composed turn are not yet wired — the composer
  edits via code today).
- **The seL4 backends** (framebuffer renderer + channel transport, §5).

## 7. Build-out lanes (HORIZONLOG)

1. **Live node connection** — move reads to gpui's async executor; wire the
   `/api/events/stream` SSE push into the ReceiptInspector with `cx.notify()`.
2. **Local-custody signing** — link the SDK turn-builder behind a feature + a
   keystore; author signed envelopes for `/turns/submit`.
3. **Organ flows** — trustline / channel / mailbox composer tabs on the typed
   signed-envelope path (gated on lane 2).
4. **Proof inspector** — render `FullTurnProof` / light-client verdicts
   (`dregg-lightclient`).
5. **Interaction** — gpui action handlers, text inputs for editing the
   composed turn, cell-selection scoping across views, ⌘K command palette
   (mirroring the web shell).
6. **seL4 framebuffer backend** — a gpui renderer targeting a framebuffer cap.
7. **seL4 channel transport** — a `NodeClient::Channel` backend over an seL4
   endpoint (additive variant).
8. **Single-source the wire types** — replace `src/model/` hand-mirrors with a
   shared `dregg-wire-types` crate depended on by both node and shell.
