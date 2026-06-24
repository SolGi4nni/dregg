# NODE-REFRAME-SCOPE

A read-only design audit of the `node/` crate and the reframe ember asked for:
"'node' was always a lazy concept; get something sexed up; split
responsibilities; the node inside seL4/firmament; make the node more
transparent to deos-js."

This document scopes what is *really there* and what the reframe costs. No code
was changed. Paths are absolute; the Rust crates live at
`/Users/ember/dev/breadstuffs/` (the `metatheory/` Lean trunk is a sibling).

---

## 1. What the node ACTUALLY is today (the source, not the story)

`dregg-node` is a **binary crate** (no `lib.rs`; everything roots at
`node/src/main.rs`, ~1437 lines) totalling **~53,400 LOC across 35 modules**.
It is one fat daemon with **seven subcommands** and **~102 HTTP routes**. The
`Cargo.toml` self-description is honest about the bundling:

> "Federation node daemon — hosts an agent cipherclerk, participates in
> consensus, and serves a localhost API"

That one sentence already names three different jobs. The code names many more.

### 1.1 The subcommands (`node/src/main.rs:64-354`)

| Subcommand | What it is | LOC anchor |
| --- | --- | --- |
| `run` | The daemon: HTTP API + blocklace consensus + prove pool + genesis seeding | `main.rs:484` (`run_node`) |
| `init` | Generate node keypair + data dir | `main.rs:928` |
| `status` | TCP liveness probe of a running node | `main.rs:980` |
| `mcp` | Run as an MCP (stdio JSON-RPC) server for AI assistants | `main.rs:1016` (`run_mcp`) |
| `genesis` | Generate devnet genesis (keys/genesis.json/env) | `genesis.rs` |
| `register-federation` | Out-of-band cross-federation trust setup | `main.rs:1329` |
| `relay` | Run as a **hosted inbox relay operator** (a wholly separate service) | `main.rs:1055` (`run_relay`) |

The `relay` subcommand alone (`relay_service.rs`, 1701 LOC) is a different
product wearing the same binary — strong evidence of the "lazy bundle."

### 1.2 The node's real responsibilities (enumerated)

Reading `main.rs::run_node`, `state.rs::NodeStateInner`, `api.rs`,
`turn_proving.rs`, and the organ services, the node DOES all of:

1. **Hosts an operator cell + cipherclerk.** `NodeStateInner.cclerk:
   AgentCipherclerk` (`state.rs:117`). The operator IS a first-class cell,
   `derive_raw(public_key, H("default"))`, with balance/nonce/state — served at
   `GET /api/node/identity` (`api.rs:1558`). **The node already exposes itself
   as a cell.**
2. **Holds the canonical ledger.** `NodeStateInner.ledger: Ledger`
   (`state.rs:119`). Served at `/api/cells`, `/api/cell/{id}`
   (`api.rs:1562-1563`).
3. **Runs the executor / produces verified state.** Via the producer-mode
   inversion: the verified Lean executor is the authoritative producer, Rust is
   a differential (`state.rs:30-50`, `lean_producer_enabled` at `state.rs:217`;
   `executor_setup.rs::execute_via_producer`).
4. **Proves every finalized turn (when armed) and serves the proofs.**
   `turn_proving.rs::prove_and_verify_finalized_turn` (`turn_proving.rs:556`)
   generates a composed full-turn STARK, **gates acceptance on the proof
   verifying**, persists it, and serves it at `GET /api/turn/{hash}/proof`
   (`api.rs:1577`). Freshness/capability variants at `turn_proving.rs:830/968/1045`.
5. **Runs consensus + finality.** Blocklace (Cordial Miners) in EVERY config
   incl. solo (`main.rs:808`, `blocklace_sync.rs` 5984 LOC), finality gate calls
   the Lean `dregg_blocklace_finalize` (`finality_gate.rs`).
6. **Serves attested state to light clients.** Roots/checkpoints/blocks/receipts
   (`api.rs:1559-1611`), starbridge cross-chain feeds (`api.rs:1578-1590`).
7. **Coordinates intents + atomic multi-party turns + conditionals/promises.**
   Intent pool (`state.rs:133`), `pending_turns: PendingTurnRegistry`
   (`state.rs:146`), atomic 2PC (`state.rs:278`), conditional turns
   (`state.rs:142`).
8. **Holds federation identity/keys/threshold-decryption shares + DKG.**
   `known_federations`, `federation_id`, `threshold_key_share`
   (`state.rs:156-182`), `dkg_service.rs`.
9. **Runs five "organ" services** merged into the router (`api.rs:1747-1764`):
   storage gateway (`/storage/*`), trustlines (`/trustline/*`), channels
   (`/channels/*`), equivocation court (`/court/*`), DKG (`/dkg/*`).
10. **Serves an MCP tool surface** (`mcp.rs`, 10505 LOC) and a WebSocket live
    feed (`ws.rs`: roots, revocations, receipts, invalid-bundles, intents).
11. **Is the relay operator** (separate subcommand, `relay_service.rs`).

That is at least **eleven distinct responsibilities** in one struct
(`NodeStateInner` has ~50 fields, `state.rs:115-349`). "Node" is indeed a
catch-all noun for "the process that happens to hold all of this."

---

## 2. The reframe: node-as-a-HOST-CELL

### 2.1 The thesis (and why it is sound)

The dregg through-line is: *a turn is the exercise of an attenuable
proof-carrying token over owned state, leaving a verifiable receipt.* A **cell**
is the unit of sovereign owned state. The node holds an operator cell and a
ledger and produces verified turns — it already behaves like *the world's own
cell*. Naming it as a **host-cell** (a sovereign cell whose business is to host
and serve other cells across distance) makes three things fall out:

- **(a) Transparency to deos-js** — if the node is a cell, deos-js inspects and
  drives it with the SAME `reflect`/`fire` it uses for any cell (the reflexive
  image: the world appears inside the world).
- **(b) A natural firmament endpoint** — one host-cell *across distance* is
  exactly `firmament`'s unified `Capability { target, rights }`. The node stops
  being "an external daemon the cockpit HTTPs to" and becomes a `Target` the
  router resolves.
- **(c) Clean splitting** — a host-cell DELEGATES rather than bundles:
  execution → executor, serving → surface, mesh → net, intents → coord.

**Is it sound given the real code? Yes — and it is already half-true.**

- The node already wraps a cell + ledger and already exposes itself at
  `/api/node/identity` and `/api/node/producer` (so "self-as-cell" is not new;
  it is under-named).
- The cell model is rich enough: a `Cell` carries 16 fixed `fields` + an
  unbounded `fields_map` overflow + a `heap` + 8 kernel `system_roots` + a
  `delegate: Option<CellId>` + `CellMode::{Hosted, Sovereign}`
  (`cell/src/cell.rs:184-227`, `cell/src/state.rs:101`). A node-cell's
  identity/federation-status/ledger-summary fit comfortably as slots.
- Firmament ALREADY has the host abstraction the node should resolve through:
  `Capability { target: Target, rights: Rights }` with
  `Target::{Local, Distributed, Surface, HostPd}` and a backing-agnostic
  `FirmamentRouter` (`sel4/dregg-firmament/src/lib.rs:1-46`,
  `router.rs:60-149`). The node-cell is a `Target::Distributed { cell }` (a real
  executor turn) or, when co-resident, a `Target::HostPd` endpoint.

### 2.2 What is NOT the right abstraction (a trap to avoid)

`deos-hermes/src/host.rs::DreggHost` is **NOT** the host the node should become.
`DreggHost` is an **OS process jail for agents** — it confines a hermes agent
subprocess (macOS Sandbox / Linux seccomp, all file/exec/net denied, one
cap-gated socket), `host.rs:120-195`. That is effect-path *process*
confinement, orthogonal to the *cell/ledger* hosting the reframe is about. Reuse
the NAME-shape ("host"), not this type.

The genuine "host" already in the tree is the **firmament backing set**
(`DistributedBacking`, `SurfaceBacking`, `HostPdBacking`) plus the **executor-PD**
(`sel4/dregg-firmament/src/executor_pd.rs`) which boots a real `TurnExecutor`
over a real `Ledger` on the semihost today. The node-cell should resolve through
those, not invent a parallel host.

### 2.3 Is "a cell that hosts a sub-ledger" feasible? (Honest limit)

Two readings of "host-cell":

- **Reading A — the node is the world's representative cell** (a sovereign cell
  whose slots are identity + federation status + a commitment to the ledger it
  serves, and whose turns are gated by held authority). **Feasible now.** The
  cell model and delegation chain (`spawn_child`, `delegate`,
  `cell/src/delegation.rs`) already support this; nothing in the ledger needs
  redesign.
- **Reading B — the cell literally NESTS a sub-ledger inside it** (containment:
  a cell owns its own private `Ledger`). **Not supported today.** The `Ledger`
  is a flat singleton (`cell/src/ledger.rs:326`); cells are peers in it, not
  containers of it. Reading B would need a new `LedgerContainment` concept,
  scoped CellId namespaces, and cross-ledger authority flows — a large refactor
  with open formal questions (it touches conservation and the apex fold).

**Recommendation: pursue Reading A.** It delivers all three payoffs (a)/(b)/(c)
without redesigning the ledger. Reading B is a separate, much larger campaign
(and may not be wanted — sovereign cells already keep state locally and sync a
commitment, `ledger.rs:229-272`, which gets most of containment's value without
nested ledgers).

---

## 3. The responsibility split (what the lazy "node" should delegate)

A host-cell delegates; it does not bundle. The split that the firmament `Target`
set and the existing crates already imply:

| Concern (today, in `node/`) | Delegate to | Already exists? |
| --- | --- | --- |
| Run the executor / produce verified state | **executor** (`exec-lean`, `turn`, the firmament executor-PD) | Yes — `executor_setup.rs`, `executor_pd.rs` boots it |
| Serve attested state / proofs to clients | **surface** (a serving face: HTTP/SSE/WS + `Target::Surface`) | Partly — `api.rs` is the de-facto surface; not yet a named crate |
| Peer the network / gossip / mesh | **net** (`dregg-net`, `blocklace`, gossip) | Yes — `blocklace_sync.rs`, `gossip.rs`, `dregg-net` |
| Intents / coordination / atomic 2PC | **coord** (`dregg-coord`, `dregg-intent`) | Yes — already separate crates the node merely orchestrates |
| Consensus + finality | **consensus** (`blocklace` + Lean finality gate) | Yes — `finality_gate.rs` |
| Federation identity / DKG / threshold | **federation** (`dregg-federation`, `dkg_service`) | Yes |
| Organ services (storage/trustline/channels/court) | their own **service crates** (most already exist as modules) | Module-level, not crate-level |
| Relay operator | **its own binary** — this does not belong in `node` at all | Yes — fully separable today |

The encouraging finding: **most of these are ALREADY separate crates** that the
node merely *wires together* in `run_node`. The reframe is largely **renaming +
re-drawing the seam**, not re-implementing. The host-cell becomes the thin
orchestrator that holds the identity and DELEGATES to these backings, replacing
the 50-field `NodeStateInner` god-struct with a cell + a set of delegated
services.

---

## 4. The deos-js transparency path

### 4.1 Where deos-js stands (the real seam)

- deos-js models a cell as `Applet`/`CellModel` (`deos-js/src/applet.rs:67-174`):
  fields as `BTreeMap<Slot, FieldElement>`, nonce, affordances fired as cap-gated
  turns.
- It reflects any cell via `deos-reflect`'s `reflect_cell` →
  `Inspectable { kind, title, fields }` (`deos-reflect/src/substance.rs:107-189`)
  and projects to JSON through `reflect_binding` (`deos-js/src/reflect_binding.rs`).
- Its reactivity is fine-grained on `(cell, slot)`:
  `BindingRegistry::invalidate(SourceEvent{cell, slot})` wakes only the bindings
  that read that slot (`deos-js/src/signals.rs:82-187`) — the recent commit
  `c38d17ed3`.
- The seam to a live backend is the **`WorldSink` trait**
  (`deos-js/src/attach.rs:43-66`): `with_ledger(&dyn FnMut(&Ledger))` +
  `fire_effects(...) -> [u8;32]`. `AttachedApplet` already drives a live World
  through it.

### 4.2 The gap and the smallest path

**deos-js does NOT see the node at all today.** It runs against an embedded
`DreggEngine` (single-cell world) or an attached in-process `World`. There is no
node concept and **no self/host/system cell** anywhere in deos-js.

The transparency path is therefore exactly:

1. Make the node implement `WorldSink` over its HTTP/IPC (translate
   `with_ledger` → a ledger snapshot/replica, `fire_effects` → a turn POST). The
   trait is small and already the intended seam.
2. Model the node's own status as **cell slots on the node-cell** (federation
   status, peer count, ledger height, producer mode). Then `deos.cell(node_id)
   .reflect()` renders the node like any other cell, and a binding on
   `(node_cell, federation_status_slot)` re-evaluates only when that slot moves.

Step 2 is the load-bearing one and it is mostly **design** (which slots), not
new machinery — the reflect/reactive/JSON layers are parametric over any
`Ledger` and need no change. This is the reflexive-image payoff: the world's own
node appears inside deos-js as a cell.

---

## 5. The seL4 / firmament fit ("the node inside seL4")

The firmament crate already builds the exact unification ember is pointing at:

- **One handle across distance**: `Capability { target, rights }` with
  `rights: dregg_cell::AuthRequired` shared verbatim; `is_attenuation`
  (`granted ⊆ held`) is the single gate at every backing
  (`sel4/dregg-firmament/src/lib.rs:1-46`). Adoption is attenuation at both ends.
- **The `n=1` collapse**: on one seL4 box the distributed bounds collapse to
  strong-local (immediate revocation, synchronous commit) — `lib.rs:35-46`,
  `Bounds::LOCAL`. The node-cell, when co-resident, gets strong-local guarantees
  for free.
- **The executor-PD boots**: a real `TurnExecutor` over a real `Ledger` runs in
  a PD on the EmulatedKernel today, with a pure-compute cap partition
  (`turn_in` READ, `commit_out` RW; no device/NIC cap) —
  `sel4/dregg-firmament/src/executor_pd.rs`. The verified Lean closure
  ELF-recompiles and runs one turn (`sel4/dregg-pd/executor-pd/README.md`).
- **The host/endpoint template already exists**: `HostPdBacking` registers
  confined endpoints reached over a control socket and routes invocations
  through the same `is_attenuation` gate (`sel4/dregg-firmament/src/host_pd.rs`).
  Surface migration shows authority-grant and live-transport as two independent
  moves.

So "the node inside seL4" maps cleanly: **the node-cell is a
`Target::Distributed { cell }`** (its turns are real executor turns) whose
serving leg, when co-resident, becomes a `Target::HostPd`/surface endpoint the
firmament router resolves *without the app branching on it*. **This is NOT
greenfield** — the router, the backings, the attenuation law, and a booting
executor-PD are all present. The remaining work is wiring the node's
identity/socket into the firmament registry and routing client reach through a
`Target` instead of a raw HTTP base URL.

---

## 6. The smallest real first step (tractable now)

Do the cheapest move that makes the reframe *visible and true*, before any
refactor:

> **Expose the node's own runtime state AS a cell that deos-js can reflect.**

Concretely:
1. Define the node-cell's status slots (identity, federation_id, committee_epoch,
   peer_count, ledger_height, producer_mode, finality_height). These already
   exist as fields on `NodeStateInner` and are already served piecemeal at
   `/api/node/identity`, `/api/node/producer`, `/status` — this step *collects*
   them onto one cell view, it invents nothing.
2. Implement `WorldSink` for the node (HTTP-backed `with_ledger` + `fire_effects`)
   so `deos.world.cells()` and `deos.cell(node_id).reflect()` work against a live
   node.

That single step delivers payoff (a) (deos-js transparency) end-to-end, validates
the host-cell framing against the live executor, and commits to nothing
irreversible. The crate split (§3) and the firmament `Target` wiring (§5) follow
as separate, larger lanes once the cell view exists.

**Tractable vs. big-refactor:**

- *Tractable now*: the §6 cell-view + `WorldSink` step; renaming the binary and
  pulling `relay` out into its own binary; collecting the self-status endpoints.
- *Medium*: routing client reach through a firmament `Target` instead of a raw
  URL; turning `api.rs` into a named **surface** crate.
- *Big refactor*: dissolving the 50-field `NodeStateInner` god-struct into a
  host-cell + delegated services (Reading A); this is desirable but should follow
  the small step, not precede it.
- *Out of scope / separate campaign*: Reading B (cells that nest sub-ledgers) —
  a new ledger-containment model with open formal questions.

---

## 7. The name

Kill "node." It says nothing — every distributed system has a "node." The
reframe wants a noun for *a sovereign vessel that hosts cells and serves them
across distance*. Candidates and the case:

| Name | Says | Against |
| --- | --- | --- |
| **Hearth** | a warm home that hosts and serves; cells gather at it; pairs with the "firmament" register | slightly cozy/soft |
| **Berth / Mooring** | a place a vessel docks across distance | maritime metaphor doesn't carry "hosts cells" |
| **Vessel** | a container that holds and carries cells | generic; collides with "vessel" in many codebases |
| **Host** | accurate (host-cell) | overloaded (`DreggHost` already exists for the agent jail — collision) |
| **Firmament-node** | ties to the seL4 unification | still contains "node" |

**Recommendation: `Hearth`.**

Reasoning: it reads as *the place cells live and are served from* (a host that
warms a neighbourhood of cells), it pairs naturally with **firmament** (sky over
hearth — the cap-across-distance reach over the local home), it is unclaimed in
the tree (no collision, unlike `Host`/`DreggHost`), and "a hearth-cell" /
"the Hearth hosts these cells" / "reach a Hearth across the firmament" all read
as intended sentences. The host-cell is a **Hearth**: a sovereign cell whose
purpose is to host other cells and serve them — locally with `n=1` strength,
seamlessly across distance as the bounds relax.

If a more neutral register is wanted, **`Vessel`** is the runner-up (vessel-for-
cells-across-distance, the literal gloss ember asked for), accepting the mild
genericity.

---

## Appendix — load-bearing anchors

| Claim | Anchor |
| --- | --- |
| Node is a binary, no lib, ~53K LOC, 35 modules | `node/src/` (`wc -l src/*.rs`) |
| Seven subcommands incl. a separate `relay` service | `node/src/main.rs:64-354`, `run_relay` at `:1055` |
| `NodeStateInner` ~50-field god-struct | `node/src/state.rs:115-349` |
| Node already exposes itself as a cell | `GET /api/node/identity` `api.rs:1558`; `cclerk` `state.rs:117` |
| ~102 HTTP routes, five organ services merged | `node/src/api.rs:1555-1764` |
| Node proves+verifies every finalized turn, serves proof | `turn_proving.rs:556`; `GET /api/turn/{hash}/proof` `api.rs:1577` |
| Producer-mode authority inversion (Lean authoritative) | `state.rs:30-50,217`; `executor_setup.rs::execute_via_producer` |
| Firmament unified cap + router + n=1 collapse | `sel4/dregg-firmament/src/lib.rs:1-46`, `router.rs:60-149` |
| Executor-PD boots a real executor in a PD | `sel4/dregg-firmament/src/executor_pd.rs`; `sel4/dregg-pd/executor-pd/README.md` |
| HostPd endpoint template (same attenuation gate) | `sel4/dregg-firmament/src/host_pd.rs` |
| `DreggHost` is an agent OS-jail, NOT the host to become | `deos-hermes/src/host.rs:120-195` |
| Cell model is field-rich (16 + overflow + heap + roots + delegate) | `cell/src/cell.rs:184-227`, `cell/src/state.rs:101` |
| Flat ledger; no cell-nests-ledger (Reading B unsupported) | `cell/src/ledger.rs:326` |
| deos-js seam to a live backend is `WorldSink` | `deos-js/src/attach.rs:43-66` |
| deos-js reflect + (cell,slot) reactivity is parametric | `deos-js/src/signals.rs:82-187`; `deos-reflect/src/substance.rs:107-189` |
| deos-js has NO node/self/host cell today | (absence; `deos-js/src/` has only `Applet` + `AttachedApplet` targets) |
