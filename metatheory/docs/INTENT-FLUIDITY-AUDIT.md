# INTENT / CO-TURN & TURN-FLUIDITY AUDIT

*Read-only source audit, 2026-06-24. Two braided worries, one question: did the
Intent / co-turn get **orphaned** (built-but-not-wired, the "house-capacities
drift"), and is a turn **"trapped in the forest where it was committed"** — or is
there a live mechanism that lets a turn FLOW between contexts?*

Discipline: **verify the source**. Every claim below carries a `file:line` and a
verdict on one of three rungs:

- **ALIVE-WIRED** — a live `Effect` / a live protocol path that *production* code
  (a running server, the cockpit, a client, the live executor's apex) actually
  reaches.
- **PROVEN-DISCONNECTED** — real, compiling, sorry-free code (Lean theorems /
  Rust structs) that *only tests* (or a re-export) call; nothing live drives it.
- **ASPIRATIONAL** — a sketch / stub / transport that no production binary runs.

The repo split: the **Lean proof tree** is at `metatheory/` (this repo); the
**Rust workspace** is at `/Users/ember/dev/breadstuffs/`. Both were read at HEAD.

---

## HEADLINE

**The Intent got lost at the wire, and the turn IS trapped in its forest — both
are real, both have the same root cause, and the bridge that would cure both is
*proven but not wired*.**

1. **The Intent / co-turn is partially orphaned.** The pieces all exist and
   most are individually proven/tested, but **no single live path stitches them
   together**:
   - The node mounts `/intents` on a real port, but **submit dead-ends in an
     in-memory `HashMap` and never commits a turn**; the only commit path
     (`/intents/fulfill`) **has zero live clients** (only an MCP-stdio operator
     tool and in-process library calls reach it).
   - **Intents are gossiped onto the network but never received** — the node's
     receive funnel drops every variant except `PublishTurn`.
   - The dedicated **co-turn wire vocabulary** (`ProposeAtomicTurn` /
     `VoteAtomicTurn` / `CommitAtomicTurn` / `PublishPipeline`) is **dead** —
     defined in `net`, never constructed-and-sent, never received.
   - The `coord` 2PC engine is **real production code but single-coordinator +
     HTTP-fan-in**; it cannot complete over the peer mesh, and its
     entangled-diff / private-leg pieces ember named are **`#[cfg(test)]`
     differentials** against the Lean models — test-only, not production wiring.

2. **A committed turn is structurally bound to ONE linear chain.** In Lean a
   turn is `t :: s.log` on a single `RecChainedState.log`, and the per-step
   invariant *requires* `s'.log = t :: s.log`. There is no executor operation
   that lifts a committed turn off its log and re-stitches it elsewhere. The
   flow mechanisms that *should* unbind it — branch-and-stitch, the un-turn,
   distributed time-travel — are **PROVEN-DISCONNECTED**: real, sorry-free,
   test-green, but **nothing a user runs branches, stitches, or un-turns a
   turn.** The live cockpit reaches only a *read-only reversibility display.*

3. **They are the same question, and the Intent/co-turn IS the intended bridge.**
   The co-turn (a joint forest committed across cells) is exactly the vehicle by
   which a turn would stop being a private cons onto one chain and become a
   shared, re-stitchable object. That vehicle is built and largely proven and
   **not wired end-to-end.** The smallest real step from "trapped" to "flowing"
   is to wire ONE of these existing-and-proven seams to a live path.

---

# PART 1 — THE INTENT / CO-TURN

## 1a. Node Intent HTTP API — `node/src/api.rs`

The server is genuinely live: `router_with_cors()` (`api.rs:1538`) is assembled,
`main.rs:876` calls it, `main.rs:900` binds a `TcpListener`, `main.rs:916` runs
`axum::serve`, reached from the live `run_node` subcommand (`main.rs:407`). The
intent routes are in `protected_routes` (`api.rs:1678`), HTTP-reachable behind
`require_auth`.

| Piece | file:line | Verdict | Disconnection |
|---|---|---|---|
| `IntentSubmitResponse` / `IntentListEntry` | `api.rs:583` / `api.rs:802` | — | type defs |
| `POST /intents` → `post_intent` | route `api.rs:1678`, handler `api.rs:3827` | **ALIVE-WIRED (server) but COMMIT-ORPHANED** | validates, content-addresses, then `s.intent_pool.insert(...)` into a `HashMap` (`api.rs:3858`, pool type `state.rs:134`), emits a WS event, gossips — and **ends** (`api.rs:3879`). **Never calls coord, never calls the executor, never commits a turn.** No background task drains the pool. |
| `GET /intents` / `GET /api/intents` → `get_intents` | `api.rs:4365` | ALIVE-WIRED (read-only list) | pulls from the same pool |
| `POST /intents/fulfill` → `post_fulfill_intent` | route `api.rs:1690`, handler `api.rs:4382` | **ALIVE-WIRED, a REAL commit** | enforces payer==creator (`api.rs:4404`); `api.rs:4469` calls `dregg_intent::fulfillment::execute_fulfillment_flow_verified` (`intent/src/fulfillment.rs:1016`), which verifies and settles a value-moving leg through the **verified ledger** (`settle_ring_verified`, `fulfillment.rs:1050`), returns a real `TurnReceipt`, emits a `Receipt` event (`api.rs:4483`). This leg genuinely commits. |

**Client side — PROVEN-DISCONNECTED.** A whole-workspace grep for any HTTP client
POSTing to `/intents`, `/intents/fulfill`, `/intents/encrypted`, or `/api/intents`
returns **zero callers**. The matches are all DFA-router *classification* tables
that map the path glob to a label string (`wire/src/dfa_router.rs:338`,
`teasting/src/router_sim.rs:117`, `preflight/src/checks/routing.rs:29`,
`dfa/examples/builder_api.rs:103`) — they never contact a node — plus a wasm
doc-comment and the Discord bot's own unrelated `/api/intents/recent`
(`discord-bot/src/http_server.rs:255`). `dregg-sdk-net/src/mailbox.rs:420`
`submit_intent` operates on a *different* `MailboxTurnIntent` mailbox type, not the
node route. SDK uses of `dregg_intent` (e.g. `sdk/src/cipherclerk.rs:4281`) call
`execute_fulfillment_flow_verified` **in-process**, never over HTTP.

**Secondary live surface — MCP stdio.** `Command::Mcp` (`main.rs:435`) →
`mcp::run_stdio` exposes `tool_fulfill_intent` (`mcp.rs:2967`) + a submit tool
(`mcp.rs:2944`). This is a live *local, single-user, stdio* path to the same pool +
fulfill logic — operator-driven, not node-to-node or SDK traffic.

**coord vs intent:** the intent commit path runs through **`dregg-intent`**
(`intent/`), **not** `dregg-coord`. `dregg_coord` is wired in `api.rs` *only* into
the separate `/api/turn/atomic` 2PC handlers (`api.rs:5112`, `5175`, `5334`).

## 1b. The `intent/` crate — `intent/src/`

A large engine (`fulfillment.rs` 118KB, `trustless.rs` 129KB, `matcher.rs`,
`solver.rs`, `pir.rs`, `gossip.rs`). `verified_settle.rs` + `verified_gate.rs`
route the per-leg verified-executor cross-check through a `verified_gate` SEAM
(`intent/Cargo.toml` header). The fulfillment commit path is **ALIVE-WIRED** *when
reached* (it is the body behind `/intents/fulfill` and the in-process SDK calls).
Verdict: **the engine is real and the fulfill leg commits; it is reachable, but
the only live caller is the in-process SDK / the MCP tool — not a network client.**

## 1c. The `coord/` crate — `coord/src/`

`coord/src/lib.rs:1` documents three layers: causal chaining, atomic multi-party
2PC, Stingray bounded counters. Production modules: `atomic.rs`, `budget.rs`,
`causal.rs`, `shared_budget.rs`, `verified_gate.rs`.

- `atomic::{AtomicForest, Coordinator, Vote, Decision, ProposeMessage,
  CommitMessage, AbortMessage}` (`coord/src/atomic.rs`) — **ALIVE-WIRED
  in-process**: driven by the node's HTTP endpoints `POST /turn/atomic`
  (`api.rs:5175`) and `POST /turn/atomic/vote` (`api.rs:5231`).
- **BUT it is single-coordinator + HTTP-fan-in, NOT peer-mesh.** When the node
  "broadcasts to peers" (`api.rs:5201`) it does **not** send `ProposeAtomicTurn`;
  it wraps a 2-field JSON stub `{"type":"atomic_proposal",...}` and gossips it via
  `PublishTurn` (`api.rs:5209`). The receiving peer tries to decode that JSON as a
  `BlocklaceGossipMessage` (`blocklace_sync.rs:1739`), fails, and drops it. Votes
  reach the coordinator only by direct HTTP POST. **A multi-party atomic turn
  cannot complete over the mesh.** → **PROVEN-DISCONNECTED (single-node).**
- **`entangled_diff` (`coord/src/lib.rs:88`), `private_leg` (`:83`), `coord_diff`
  (`:94`) are ALL `#[cfg(test)]` modules.** They are *differential tests* against
  the Lean models `Dregg2/Distributed/{EntangledJoint,PrivateLeg}.lean` and
  `Dregg2/Coord/*` (`entangled_diff.rs:1`, `private_leg.rs:1`). They are NOT
  production wiring — exactly the "smoke-test in the periphery ≠ wired into the
  living protocol" pattern. → **PROVEN-DISCONNECTED (test-only differential).**

## 1d. Network flow — `net/src/message.rs`

`PeerMessage` (`net/src/message.rs:14`). The intent/co-turn-bearing variants:

| Variant | file:line | Sent (live) | Received+handled (live) | Flows peer↔peer | Verdict |
|---|---|---|---|---|---|
| `PublishTurn` | `:18` | ✅ `node/src/gossip.rs:40` | ✅ `blocklace_sync.rs:1734` | ✅ | **ALIVE-WIRED** (the one live path; carries blocklace consensus) |
| `PublishIntent` | `:49` | ✅ `gossip.rs:54/67`, callers `ws.rs:303`, `api.rs:3872/4213` | ❌ **dropped** | ❌ | **PROVEN-DISCONNECTED (send-only)** |
| `ProposeAtomicTurn` | `:56` | ❌ never | ❌ never | ❌ | **PROVEN-DISCONNECTED (dead variant)** |
| `VoteAtomicTurn` | `:63` | ❌ | ❌ | ❌ | **PROVEN-DISCONNECTED (dead)** |
| `CommitAtomicTurn` | `:70` | ❌ | ❌ | ❌ | **PROVEN-DISCONNECTED (dead)** |
| `PublishPipeline` | `:78` | ❌ | ❌ | ❌ | **PROVEN-DISCONNECTED (dead, no test)** |

The load-bearing receive funnel (`node/src/blocklace_sync.rs:1734`):

```rust
let turn_data = match message {
    PeerMessage::PublishTurn { turn_data, .. } => turn_data,
    _ => return,                       // ← every non-PublishTurn variant dropped
};
```

`topic_intents` is `join_topic`'d for *publishing only* (`blocklace_sync.rs:1521`);
the only live `gossip.subscribe()` is on the blocklace topic
(`blocklace_sync.rs:1496`). So a gossiped intent is disseminated into the mesh and
**consumed by no node-level handler.** No "entangled diff" or "conditional/partial
turn" variant exists in `PeerMessage` at all.

## 1e. CapTP promise-pipelining — `captp/src/pipeline.rs`, `wire/`

- The pipeline does NOT ride `PeerMessage`/gossip; it uses an in-memory outbox
  (`captp/src/pipeline.rs:496`) the networking layer "should drain" (`:495`).
- Real transport = `wire::WireMessage::PipelinedMsg` over `wire/src/connection.rs`
  TCP. **Receive is wired** (`wire/src/server.rs:2793` →
  `pipeline_bridge.on_pipeline_message`), but **send-back is OPEN**:
  `drain_pipeline_outbox` (`wire/src/server.rs:1086`) has **zero callers**; the
  SDK mirror `CapTpClient::drain_wire_outbox` is called **only in its own tests**.
- **The transport is never run in production:** `SiloServer::run`
  (`wire/src/server.rs:1465`, the TCP accept loop carrying `PipelinedMsg` /
  `PresentHandoff`) has no callers in `node/`, `starbridge-v2/`, or
  `starbridge-apps/` — only wire's own `bin/` and unit tests. `captp/src/netlayer.rs`
  ships only `InProcessNetlayer` (`:375`) and `RelayNetlayer` (`:675`,
  `Arc<Mutex<MessageRelay>>` = in-process shared memory) — neither is a socket,
  neither instantiated outside captp's tests.

→ CapTP pipelining/handoff: **ASPIRATIONAL** (real, but the transport runs only in
test/demo binaries; even there the result-return path is unwired).

## 1f. The Lean tier — joint-turn / await / coordination + the partial-turn algebra

Two cleanly-separated strata, both in the build graph (imported by `Dregg2.lean`),
both sorry-free.

**Stratum A — the categorical joint-turn / coordination tower:
PROVEN-DISCONNECTED (parallel-abstract).** None of these reference a real executor
type (`RecordKernel` / `RecChainedState` / `Turn` / `FullAction`); they quantify
over their *own* abstract vocabulary.

| File | Main theorems | Quantifies over | Verdict |
|---|---|---|---|
| `Dregg2/JointTurn.lean` | `joint_sound` (`:186`), `joint_sound_needs_binding` (`:217`), `atomicity_as_proof` (`:328`, "joint commit ⇔ cumulative-AND, no 2PC coordinator"), `family_joint_sound` (`:379`) | `TurnCoalg Obs AdmissibleTurn` (abstract, `:31`) | PROVEN-DISCONNECTED |
| `Dregg2/Hyperedge.lean` | `hyperedge_sound` (wide-pullback unification) | `TurnCoalg` (`:36`) | PROVEN-DISCONNECTED |
| `Dregg2/Await.lean` | `commit_resumes_once` (`:278`), `rollback_discards_continuation` (`:264`), `runtime_guard_is_double_spend` (`:196`), `four_faces_unify` (`:376`) | its **own** `Op` inductive (`:65`), NOT the real `Effect` | PROVEN-DISCONNECTED |
| `Dregg2/Coordination.lean` | `projection_sound` (`:373`, MPST/EPP), `deadlock_initial_counterexample` (`:662`), `iconfluent_fragment_crossgroup_free` (`:415`) | own `GlobalType`/`Role`/`Label` | PROVEN-DISCONNECTED |
| `Dregg2/Projection.lean` | `epp_correspondence` (`:105`, an explicit re-export of `Boundary.boundary_law`) | abstract | PROVEN-DISCONNECTED |
| `Metatheory/Categorical.lean` | `measure_tensor` / `measure_invariant` | `[Category C][MonoidalCategory C]` | PROVEN-DISCONNECTED |

**Stratum B — the executable partial-turn realization: ALIVE-WIRED** to the real
`RecChainedState` / `RecordKernel` substrate via `execFullTurn` / `stateStep`.

| File | Keystone | Rides | Verdict |
|---|---|---|---|
| `Dregg2/Exec/ConditionalTurn.lean` | `condTurn_atomic` (`:226`), `condTurn_conserves` (`:277`), `condTurn_dependency_sound` (`:417`, Kahn topo, no use-before-define), `condTurn_forward_sim` (`:572`) | `execFullTurn` over real `RecChainedState`; imports `TurnExecutorFull` + `Await` (`:67`) | **ALIVE-WIRED** |
| `Dregg2/Exec/GuardedHole.lean` | `holeFill_binds_in_circuit` (`:59`, a fill binds δ AND guard), `holeFill_rejects_guard_violation` (`:67`, fail-closed) | `stateStep` over real `RecChainedState` | **ALIVE-WIRED** |
| `Dregg2/Exec/CapTP.lean` | `pipelining_preserves_seam`, Granovetter handoff family (`handoff_non_amplifying`, …) | the real Spec.Guard authority seam | **ALIVE-WIRED** (one documented OPEN: cross-vat GC liveness) |

**The one residual seam in Stratum B:** the conditional/guarded-hole executors ride
`TurnExecutorFull.FullAction` (a 5-op set: balance/delegate/revoke/mint/burn) over
`RecChainedState`, **not** the richer apex `FullActionA` / `Turn` vocabulary that
`FullForestAuth` / `recCexec` use and that the light client verifies. So they ride
the real `RecordKernel` substrate but are one op-set narrower than the full live
apex.

### Part-1 verdict

**The Intent / co-turn is PARTIALLY ORPHANED, with three precise disconnections:**

1. **Submit→commit gap.** `post_intent` dead-ends in a `HashMap` (`api.rs:3879`);
   no live consumer turns a submitted intent into a committed turn.
2. **Wire gap.** Intents are gossiped but dropped on receive
   (`blocklace_sync.rs:1736`); the co-turn wire vocabulary
   (`ProposeAtomicTurn`/`VoteAtomicTurn`/`CommitAtomicTurn`/`PublishPipeline`) is
   **dead** — defined, never sent, never received.
3. **Client gap.** No CLI/SDK/deos/demo client ever HTTP-POSTs an intent; the only
   live driver is an MCP-stdio operator tool and in-process SDK calls.

The Lean abstract joint-turn tower (`JointTurn`/`Hyperedge`/`Coordination`/…)
**proves the co-turn is sound** (`joint_sound`, `atomicity_as_proof`) but quantifies
over `TurnCoalg`, not the live executor — it is a *parallel proof*, not the
semantics any live code runs. The executable conditional/guarded-hole layer IS
wired to `RecChainedState` and is the genuinely-live partial-turn realization.

---

# PART 2 — TURN FLUIDITY ("trapped in the forest")

## 2a. How a turn is BOUND to its forest (the trap, exactly)

In Lean the live record executor's state is:

```lean
structure RecChainedState where        -- RecordKernel.lean:795
  kernel : RecordKernelState
  log    : List Turn

def recCexec (s : RecChainedState) (t : Turn) : Option RecChainedState :=  -- :800
  match recKExec s.kernel t with
  | some k' => some { kernel := k', log := t :: s.log }   -- a CONS onto ONE log
  | none    => none
```

and the per-step invariant **requires** the cons (`RecordKernel.lean:808`):

```lean
def recFullStepInv (s) (t) (s') : Prop :=
  recTotal s'.kernel = recTotal s.kernel ∧      -- Conservation
  authorizedB s.kernel.caps t = true ∧          -- Authority
  s'.log = t :: s.log ∧                          -- ChainLink  ← THE TRAP
  s'.log.length = s.log.length + 1
```

A committed turn is structurally `t :: s.log` on **one** `RecChainedState.log`, and
the soundness theorem `recCexec_attests` (`:815`) *demands* `s'.log = t :: s.log`.
The call-forest layer above it (`FullForestAuth.execFullForestG`,
`FullForestAuth.lean:530`; `FullForest.execFullForestA`, `FullForest.lean:191`;
`CrossCellForest`) is a *tree of `recCexec`/half-edge steps over the same chained
state* — the cross-cell binding (CG-5, `Σδ=0`) is carried as a hypothesis, but the
result is still a fold onto chained logs.

**There is no executor operation that lifts a committed turn off its `log` and
re-stitches it onto a different chain.** That is the precise mechanical meaning of
"trapped in the forest where it was committed": a turn is a private cons; the only
sanctioned movements are *forward* (append another turn) or *not at all*.

## 2b. The flow mechanisms that SHOULD unbind it

### Branch-and-stitch (Lean: `Dregg2/Deos/BranchStitch.lean`) — PROVEN, IN BUILD, but operates on DOCUMENTS not TURNS

Imported into the build at `Dregg2.lean:660`; sorry-free; `#assert_axioms`-clean.
It proves two halves with a critical type split:

- **Part A — nesting = confinement-safety** rides the **real kernel**:
  `branch_cannot_drain_main` (`BranchStitch.lean:110`) quantifies over
  `{k k' : KernelState} {turn : Turn}` and `exec`, reusing
  `Confinement.confined_cannot_debit_attacker`. A `Virtual` branch holds no cap to
  main, so its turns *cannot debit* main — the integrity half is a real cap
  theorem over the live executor types. (Honest named residual: confinement
  confines authority/draining, **not** information — `branch_may_signal_main`,
  `:162`.)
- **Part B — the stitch IS the pushout** rides **`DocGraph`**, not turns:
  `stitch_is_pushout` (`:241`), `stitch_iconfluent_clean` (`:263`),
  `stitch_drop_explicit` (`:318`) all quantify over `DocGraph` / `merge` (the
  dregg-doc document graph), reusing `DocMerge.merge_is_lub`.

**So the *containment* of a branch is proven over real turns, but the *stitch back*
is proven over documents.** There is **no Lean theorem that stitches a committed
`Turn`/`RecChainedState.log` back into main** — the re-stitch lives at the document
layer (`DocGraph`), one layer off the turn log. This is the formal echo of the trap.

### Branch-and-stitch (Rust: `starbridge-v2/`) — PROVEN-DISCONNECTED

`starbridge-v2/src/branch_stitch.rs` models `VirtualBranch` + `Stitch` over an
abstract `DocGraph` (atoms), **not** real turns/forests. Declared
`pub mod branch_stitch` (`lib.rs:516`, `#[cfg(feature="embedded-executor")]`);
**no reference in `main.rs` or `cockpit.rs`.** Live-ish callers
(`comms_pd_source.rs:282`) are themselves only constructed by *headless bakes*
(`showcase.rs:130`, `guest.rs:246`) — not an interactive loop — plus a bench
(`perf/benches/membrane.rs:153`) and 11 of its own `#[cfg(test)]` tests
(`branch_stitch.rs:362`).

`distributed_timetravel.rs` (`run_collaborative_rewind`, `:360`) and
`two_image_firmament.rs` and `shared_fork.rs`: **zero non-test callers**; their own
headers call them "`cargo test`-able" scenarios.

### First-class reversibility / the un-turn (`turn/src/reversible.rs`) — PROVEN-DISCONNECTED

`reversible.rs:1` documents the RCCS un-turn over the real `Effect` set, with three
honest tiers (`Inversion::Clean`/`Contextual`/`Committed`). It is real and tested —
but **`undo_to` / `ReversibleHistory::new` are called only inside `reversible.rs`
itself, all under `#[cfg(test)]`** (tests at `:1247`, `:1400`, `:1587`…). Outside
`turn/`: `lib.rs:181` re-exports the names; the cockpit's `history_lens.rs` uses
`Inversion::{Clean,Contextual,Committed}` **for classification/display only** (it
calls `effect.invert(pre)` at `history_lens.rs:98` to *label* changes, never to
undo); `time_travel.rs:246` mentions `undo_to` only in a doc-comment. The live
cockpit reaches a **read-only reversibility display**
(`cockpit/panels_main.rs:886` → `history_lens::CellReversibility::from_world`),
never an actual un-turn.

### The document merge/stitch (`dregg-doc/src/merge.rs`, `history.rs`) — substrate LIVE, merge PROVEN-DISCONNECTED

`dregg-doc`'s **linear** core is genuinely live: the deos-zed editor's durable
document is a `dregg_doc::History`, and `editor.rs:345 save()` commits patches via
`doc.edit_rope(...)`. **But `save()` never merges or stitches.** Every live caller
of `History::stitch`/`merge` (`history.rs:95`/`merge.rs:30`) is a test, demo, or
example: `deos-js/program_doc.rs:130` `stitch` is only hit by
`deos-js/tests/program_source_as_document.rs`; `deos-matrix/src/membrane.rs:611`
`stitch` is under `#[cfg(test)]`; `starbridge-v2/src/stitcher.rs:171` has zero
cockpit callers; `xanadu_e2e.rs:99` is a `cargo test` demonstration.

### Event-structure / RCCS config lattice — ASPIRATIONAL (docs + the proven pieces, no assembled object)

The "turn-layer as event structure (config lattice + RCCS reversibility)" framing
lives in `docs/deos/{DISTRIBUTED-TIMETRAVEL-SEMANTICS,BRANCH-AND-STITCH-PROTOCOL}.md`
and is *realized in pieces* (the un-turn = `reversible.rs`; the confluent fragment =
`Confluence.IConfluent`; the pushout = `DocMerge.merge_is_lub`) — but **there is no
single live object that presents the turn log AS a configuration lattice you can
move within.** The reversibility is proven; the lattice navigation is not built as a
live mechanism.

## 2c. Part-2 verdict

**"Trapped in the forest" is a REAL current limitation, not a misperception.**

- A committed turn is mechanically `t :: s.log` on one chained log
  (`RecordKernel.lean:800/808`); the soundness invariant *requires* the cons. No
  executor primitive re-parents a committed turn onto another chain.
- Every mechanism that would let a turn FLOW — branch-and-stitch, the un-turn,
  distributed time-travel, the config lattice — is **PROVEN-DISCONNECTED or
  ASPIRATIONAL**: real, sorry-free, test-green code that **no live path drives**.
  The cockpit touches only a *read-only* reversibility *display* and the *linear*
  document-patch save path.
- The one place a stitch IS proven (BranchStitch Part B) operates on **`DocGraph`
  documents, not on `Turn`/`RecChainedState` logs** — so even the proof is one
  layer off the thing that's trapped.

**Is the Intent/co-turn the bridge? Yes.** A co-turn — a joint call-forest committed
atomically across cells (`coord::AtomicForest`; Lean `joint_sound` /
`atomicity_as_proof` / `EntangledJoint`) — is precisely the construct that turns a
private cons-onto-one-chain into a *shared, cross-context* turn object. The
conditional/guarded-hole executor (Stratum B, ALIVE-WIRED) is the partial-turn
machinery that lets a turn have holes resolved *elsewhere* — a turn whose
completion flows across contexts. Wiring those is the bridge from "trapped" to
"flowing."

---

# SYNTHESIS — where the co-turn/Intent actually lives, and the smallest real step

**Where it lives in the stack (honest map):**

- **Proven, deepest, parallel:** the Lean abstract tower
  (`JointTurn`/`Hyperedge`/`Coordination`/`Await`) proves the co-turn and the
  one-shot await algebra are *sound* — over `TurnCoalg`/`Op`, a parallel model.
- **Proven AND wired to the real substrate:** the executable partial-turn layer
  (`Exec/ConditionalTurn`, `Exec/GuardedHole`, `Exec/CapTP`) rides real
  `RecChainedState`/`RecordKernel` — the genuinely-live promise/hole machinery,
  one op-set narrower than the full apex.
- **Real production code, single-node:** `coord::atomic` 2PC + the node's
  `/turn/atomic*` HTTP endpoints — a co-turn you can drive *against one
  coordinator over HTTP*, but not across the peer mesh.
- **Real, but test-only / orphaned:** the `coord` entangled-diff & private-leg
  differentials (`#[cfg(test)]`); the un-turn (`reversible.rs`); branch-and-stitch
  (`starbridge-v2`, `dregg-doc` merge); distributed-time-travel scenarios.
- **Dead at the wire:** `PublishIntent` (gossiped, dropped on receive);
  `ProposeAtomicTurn`/`VoteAtomicTurn`/`CommitAtomicTurn`/`PublishPipeline` (defined,
  never sent or received); the CapTP `SiloServer` transport (no production binary
  runs it).

**The single root cause** of both worries: the dedicated co-turn / intent / stitch
*vocabularies exist and are proven in isolation, but no live path threads one of
them end-to-end* — the receive funnel
(`node/src/blocklace_sync.rs:1734`) only honors `PublishTurn`, so every richer turn
shape (intent, joint, conditional, branch) has nowhere live to land.

**Smallest real step from "trapped" to "flowing"** (each is a *wire*, not a
*build* — the proofs already exist):

1. **Make submitted intents commit.** Add the missing consumer: a background task
   (or an inline fulfill on submit when a counter-leg exists) that drains
   `intent_pool` (`api.rs:3858`) through the already-live
   `execute_fulfillment_flow_verified` (`intent/src/fulfillment.rs:1016`). Closes
   the submit→commit gap with code that already commits.
2. **Honor one co-turn variant on receive.** Extend the funnel
   (`blocklace_sync.rs:1734`) to dispatch `PublishIntent` (and/or
   `ProposeAtomicTurn`) into the existing in-process `coord`/`intent` engines —
   turning the *dead* wire vocabulary into a live mesh path. This is the literal
   bridge that lets a co-turn flow between two nodes.
3. **Promote the live partial-turn layer to a live effect.** The conditional/
   guarded-hole executor (`Exec/ConditionalTurn`, ALIVE-WIRED) already lets a turn
   carry holes resolved elsewhere; lifting `ConditionalBatch` into the first-class
   apex `Effect`/`Turn` vocabulary (closing the 5-op vs `FullActionA` seam noted in
   §1f) makes "a turn that flows" light-client-verifiable.

Any one of these is a finite wiring task over already-proven parts — which is the
honest good news under the orphaning verdict: **nothing here needs to be invented;
it needs to be connected.**

---

*Method note (for the next reader): every "PROVEN-DISCONNECTED" here was confirmed
by finding the caller set and observing it is `#[test]`/bench/demo/headless-bake or
a re-export only; every "ALIVE-WIRED" by tracing to a running server bind
(`main.rs:916`), the live receive funnel, or the build-graph import + real-executor
type quantification. Docs and memory were treated as leads, never as evidence.*
