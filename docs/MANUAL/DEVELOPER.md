# Building on dregg — the developer manual

← back to [the manual index](README.md)

This is the start-here for someone who is *not* the author, building on dregg
from a clean checkout. It orients you: the architecture, how to build the
unified workspace, and how to write your first deos-js program. For the exact
guarantees and open seams, read
[`../../metatheory/CLAIMS.md`](../../metatheory/CLAIMS.md); for the substrate
design, [`../KERNEL.md`](../KERNEL.md).

## Architecture

The whole kernel is one sentence — *a turn is the exercise of an attenuable,
proof-carrying token over owned state, leaving a verifiable receipt* — and the
codebase is the faithful realization of it.

### The core nouns

- **Cells.** A cell is a sovereign object. Everything it holds is one of four
  **substances**: *value* (linear balances — an asset *is* its issuer cell, which
  carries −supply, so every asset's sum is identically zero), *state* (a heap of
  programmable slots), *authority* (a capability tree), and *evidence* (monotone
  nullifier / commitment / epoch ledgers). Cell state types live in
  [`cell/`](../../cell/) (zero-crypto) and [`cell-crypto/`](../../cell-crypto/).

- **Capabilities.** Authority is **production under non-forgeability**: to hold a
  capability is to be able to *produce* a witness that verifies, never to merely
  assert. Authority grows only by authorized, receipt-disclosed production from
  held connectivity, and **narrows freely** — delegation can only *attenuate*
  (`granted ≤ held`), enforced at the dispatcher. Capabilities carry **caveats**
  (time-boxes, third-party discharge, rate bounds, scope) composed macaroon-style
  ([`macaroon/`](../../macaroon/)). The kernel checks the witness; it does not take
  your word.

- **Turns.** A turn is an atomic, capability-gated transition across one or more
  cells — a **forest** of effects with delegation edges. A turn that cannot
  exhibit a valid, sufficiently-empowered, fresh token chain simply does not
  execute. The kernel is **eight verbs** (`create · write · move · grant · revoke
  · shield/unshield · lifecycle · exercise`) over the four substances, with
  machine-checked minimality and completeness. Turn types + the executor +
  witness-mode/collapse live in [`turn/`](../../turn/).

- **Receipts.** Every turn leaves a receipt that binds the *whole* post-state.
  The executor is a "memory program": every field has an address in one
  domain-tagged universal space, and tampering a field the effect did not touch
  makes the turn unprovable (the *anti-ghost* property).

### The verified spine

- **The kernel ([`metatheory/`](../../metatheory/), Lean 4, library `Dregg2`).**
  This is *the system itself*: the eight-verb kernel, the gated executor
  (`execFullForestG`), the circuit IR + descriptor emission, and the assurance
  case. It is l4v-shaped: abstract spec → executable design → refinement proofs.
- **The link ([`dregg-lean-ffi/`](../../dregg-lean-ffi/)).** Compiles the Lean
  executor into `libdregg_lean.a` and exports the entry the node calls. **The
  verified executor *is* the executor** — not a model of the node, the function
  the node invokes.
- **The circuit ([`circuit/`](../../circuit/)).** STARK proofs (Plonky3,
  BabyBear, Poseidon2, FRI) attest turns *additively* — verifying never re-runs
  history — and recursive aggregation folds a whole history into one root a
  **light client** checks. The light-client guarantee is **unfoolability**: a
  client checking only the aggregate root learns authority + conservation +
  integrity + freshness for the entire history, re-witnessing nothing.
  Constraints are *emitted from Lean* as byte-pinned descriptors; the Rust prover
  interprets them and authors no constraints of its own.

### The deos layer (zero new trust)

- **deos-js ([`deos-js/`](../../deos-js/)).** Reflective scripting over the live
  world. A card's behavior is `run_js`; an attached runtime can crawl the world
  within its capability bound, drive it (`run_js` against the live World), and
  author cards as receipted patches. (Links SpiderMonkey / `mozjs`,
  single-threaded.)
- **deos-view ([`deos-view/`](../../deos-view/)).** Renders a **view-tree** to
  real pixels: `deos.ui.{vstack,row,text,bind,button,input,list,table}` →
  gpui-component widgets (`vstack→v_flex`, `button→Button`, `text→Label`,
  `bind→Label` re-read). Renderer-independent in design — the view-tree is the
  serializable contract, the renderer is one consumer.
- **The web-surface / affordance / rehydration stack
  ([`starbridge-web-surface/`](../../starbridge-web-surface/),
  [`deos-reflect/`](../../deos-reflect/)).** Cell affordances, the per-viewer
  membrane, and rehydratable snapshots — every primitive reduces to a kernel
  theorem.
- **The cockpit ([`starbridge-v2/`](../../starbridge-v2/)).** The native gpui
  cockpit that embeds the real verified executor; the dev basement an adept drops
  into. The inhabited world arises *inside* dregg, renderer-independent — the
  cockpit is one client.

### The node

The node ([`node/`](../../node/)) is a **headless** daemon: HTTP/MCP API, gossip +
blocklace DAG sync, block production driven by the Lean producer. Its state
producer is the Lean executor itself (`/status` reports `"state_producer":"lean"`).
Beyond serving turns, the node can **host userspace deos-js "private servers"** —
headless programs that hold real cells on the node's ledger and offer cap-gated
affordances players connect to and fire (see *Writing a deos-js program* below).

## Building — the unified workspace

There is **one** workspace and **one** toolchain. The trick is the
`default-members` split: the gpui / mozjs / servo heavy crates are members but
*not* defaults, so the everyday loop stays light.

- **Light core (the default loop).** A bare `cargo build` / `cargo test` operates
  on `default-members` only — the protocol / circuit / app crates, **gpui-,
  mozjs-, and servo-free**. This is fast and what you run most of the time.

  ```sh
  cargo build          # the light core only
  cargo test           # likewise
  ```

- **Heavy crates (opt in by package).** The elephants — `starbridge-v2`,
  `deos-js`, `deos-view`, `deos-matrix`, `deos-zed`, `deos-terminal`,
  `deos-hermes`, `servo-render` — build explicitly with `-p`:

  ```sh
  # `--features desktop` is REQUIRED for the cockpit. starbridge-v2's default set is the
  # gpui-free embedded executor: it is a workspace MEMBER, so anything in its default is
  # unified onto every other package by `--workspace` (a `desktop` default made
  # `servo-render` resolve `libservo` for the whole tree). A bare
  # `cargo build -p starbridge-v2` is a real, useful, much smaller build — just not the cockpit.
  cargo build -p starbridge-v2 --features desktop  # the native cockpit (gpui + libservo — heavy; use --release)
  cargo build -p deos-js           # the reflective JS runtime (pulls mozjs)
  cargo build -p deos-view         # the view-tree → pixels renderer
  ```

- **The node + CLI** (the fastest way to see a verified turn):

  ```sh
  cargo build -p dregg-node -p dregg-cli
  ./target/debug/dregg-node init --data-dir /tmp/my-dregg
  ./target/debug/dregg-node run  --data-dir /tmp/my-dregg --enable-faucet --port 8421 &
  ./target/debug/dregg --node-url http://localhost:8421 demo --passphrase pick-one
  ```

- **Toolchain.** Rolling `nightly` (pinned in
  [`../../rust-toolchain.toml`](../../rust-toolchain.toml)), edition 2024 — one
  toolchain for *all* crates including the gpui fork (which needs
  `std::hint::cold_path`).

- **The forks build for anyone.** zed, gpui-component, and stylo are **git
  dependencies on GitHub**, not local paths — a plain `git clone` + `cargo build`
  works on any machine, not just the author's.

- **A few separate workspaces (excluded):** `solana-lock`, `solana-settlement`,
  `wasm` (the in-browser executor), `sdk-py`, `pg-dregg`, `deos-zed-full`,
  `discord-bot`, `dregg-tui`, `deos-homeserver`, `durable-workflow`, and
  `forge-ci-runner` carry their own manifests (the `exclude` list in
  [`../../Cargo.toml`](../../Cargo.toml)). The everyday workspace does not pull
  them. `chain/`, `dregg-doc`, and the seL4 firmament crate are ordinary
  workspace members.

> **Note on the Lean link.** The node links `libdregg_lean.a`. If the
> `metatheory/` working tree has an in-progress proof regression, the FFI build
> script restores the last consistent seed archive and links *that*, so the node
> still builds while a proof lane is mid-flight. To pick up fresh kernel changes,
> make `lake build Dregg2.Exec.FFI` green in `metatheory/` first. See
> [`DEV-NODE-RUNBOOK.md`](../deos/DEV-NODE-RUNBOOK.md).

> **[in flux]** `cargo check --features native-full --bin starbridge-v2` after
> any cockpit edit — the cockpit's `cockpit.rs` lives in `main.rs` behind a
> `gpui-ui` cfg, so the gpui-free `--lib` suite does not compile it.

## Writing a deos-js program

A deos-js program is a card, or a server hosted headless in the node. Both build
the same vocabulary: a **view-tree** plus **cap-gated affordances** that commit
real verified turns.

### A card (a cell with a view + affordances)

A card builds a view-tree and registers affordances. The view-tree node kinds are
`deos.ui.{vstack,row,text,bind,button,input,list,table}`; a `button(label, aff,
arg)` fires affordance `aff` with `arg`, and a `bind` re-reads off the live
ledger. Sketch (the canonical counter shape):

```js
var b = deos.ui.bind("count");                       // re-reads the live field
var tree = deos.ui.vstack(
  deos.ui.text("Counter"),
  b,
  deos.ui.button("+1", "inc", 1)                      // fires the `inc` affordance
);
```

[`deos-view/`](../../deos-view/) renders that tree to real gpui-component widgets;
pressing the button fires `inc` as a cap-gated verified turn.

### A private server hosted in the node

The node hosts a userspace deos-js program as a **private server**: it mints its
own cells on the ledger and publishes a cap-gated affordance surface that players
connect to and fire against. The program uses the **`deos.server.*` API**:

- **`deos.server.spawnCell(seedHex, perms)`** — mint a fresh cell on the node's
  ledger (the "GM" superpower; defaults to open perms). Returns the new cell.
- **`deos.server.grant(toCellHex, onCellHex, required)`** — grant a capability
  over one cell to another.
- **`deos.server.defineAffordance(spec)`** — register a cap-gated affordance
  carrying a *real* `dregg_turn::Effect`. The keystone: this is the cap-gated
  turn template players fire.

On boot, the host mints the server cell, attaches the runtime to a sink over the
node's live state, runs your program (which registers cells + affordances), then
**drains** the registered surface and publishes it where the node's discovery
route reads it. A client then **fires an affordance through the node's
`/turns/submit` ingress** with a signed turn — the *same* producer-gated commit
path the HTTP signed-turn ingress runs. The cockpit is then just one client of
this headless host. Architecture + the boot flow: [`node/src/deos_host.rs`](../../node/src/deos_host.rs);
a worked example fixture is [`node/src/deos_host_e2e.rs`](../../node/src/deos_host_e2e.rs)
and [`node/tests/fixtures/gm.js`](../../node/tests/fixtures/gm.js).

### Players connect and fire

Players submit signed turns. The submit endpoints on the node include
`POST /turns/submit` (a signed envelope built by an SDK) and
`/turns/submit-encrypted`. The SDKs build these for
you — two nouns and an inescapable authorization step:
`.turn().sign().submit()`.

### The other surfaces onto the kernel

Every one of these routes authorization through the *same* verified kernel:

- **SDKs** — Rust ([`sdk/`](../../sdk/), `AgentRuntime` embeds the executor),
  TypeScript ([`sdk-ts/`](../../sdk-ts/), browser-parsable), Python
  ([`sdk-py/`](../../sdk-py/) — the default wheel is the light, client-only
  build: signing + wire codec + HTTP, no Lean link; embedding the *real* Lean
  kernel via FFI is an opt-in build feature).
- **The CLI** ([`cli/`](../../cli/), bin `dregg`) — manages keys, drives turns,
  decodes the app machines.
- **The MCP server** ([`node/src/mcp/`](../../node/src/mcp/)) — cap-gated
  AI-agent access; every tool a sub-agent calls carries a capability the node
  admits or refuses through the Lean producer gate. (For driving the *live
  embedded image* in the cockpit, see [`DREGG-MCP.md`](../deos/DREGG-MCP.md).)
- **pg-dregg** ([`pg-dregg/`](../../pg-dregg/)) — dregg capabilities as a
  PostgreSQL row-level-security + durable-workflow layer.
- **The browser playground** ([`site/`](../../site/), [`wasm/`](../../wasm/)) —
  stage, run, and *prove* turns against an in-browser wasm executor.

### Agents inhabit, confined

An AI agent in deos does not merely call an API — it **inhabits** the world: it
crawls within its capability bound, drives via `run_js` against the live World,
can read the dregg source bundled inside deos as a cap-bounded read, and authors
cards as receipted patches. It is **empowered-but-accountable**: every action is
a rewindable receipt, and the only wall is the membrane — it provably cannot
forge authority or reach into another vessel.

> **[in flux]** The dregg-as-host inversion — the agent jailed in a confined PD,
> its tools routed to containers, the live brain in-jail via a confined MCP
> tool-bridge — is partly built (real jail + dregg-tools-only effect path; the
> in-jail brain is the closing wire). See
> [`deos-hermes/DESIGN.md`](../../deos-hermes/DESIGN.md) and
> [`LOG-A-HERMES-IN.md`](../deos/LOG-A-HERMES-IN.md) (a live brain driving the
> cockpit's World via receipted `run_js` turns).

## Pointers

- **The charter + the brand** — [`HYPERDREGGMEDIA.md`](../deos/HYPERDREGGMEDIA.md) (the
  inhabited world), [`DEOS.md`](../deos/DEOS.md) (the desktop brand), and
  [`COCKPIT-UX.md`](../deos/COCKPIT-UX.md) (the cockpit's five-mode frame).
- **The guarantees + the honest opens** —
  [`../../metatheory/CLAIMS.md`](../../metatheory/CLAIMS.md) (the skeptic-facing
  ledger, build-enforced) and
  [`AssuranceCase.lean`](../../metatheory/Dregg2/AssuranceCase.lean).
- **The substrate design** — [`../KERNEL.md`](../KERNEL.md) (four substances,
  the verbs, the verified kernel).
- **THE ATLAS** — [`../../dregg-atlas/site/index.html`](../../dregg-atlas/site/index.html).
  The interactive, code-grounded map of every surface, the object-capability web,
  the game tree, and the protocol reference. **The manual is the trail guide; the
  atlas is the territory — explore the whole system there.**
