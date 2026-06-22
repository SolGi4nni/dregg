# Frontend / Product-Surface Overhaul Plan

_Assessment phase (read-only). Author: Claude Opus 4.8 (1M ctx), 2026-06-08._
_Scope guard: `site/`, `paper/`, `extension/`, `discord-bot/`, `app-framework/webgen`,
studio JS only. Lean (`Dregg2/*`), `circuit/`, `cell/`, `captp/`, `blocklace/`,
`intent/`, `sdk/src/full_turn_proof.rs` are READ-ONLY here (other workflows own them)._

This document is the diagnosis + prioritized redesign + file-level Build breakdown.
Everything below is grounded in code I read and endpoints I actually hit. Where a
thing is rough/unproven I say so.

---

## 0. Ground truth (verified this session, not asserted)

What is REAL and citable (do not overclaim past this):

- **56 effects, 29 StateConstraints, drift-guarded.** `node site/tools/gen-ontology-catalog.js --check`
  → EXIT 0, `56 effects · facet 56/56 · wire 56/56` and `29 constraints · 4 program
  kinds · 6 guards · view 29/29 · locally-evaluable 15/29`. The generator parses the
  verified Lean (`metatheory/Dregg2/Exec/TurnExecutorFull.lean` `FullActionA` +
  `requiredFacetA`, `FFI.lean` `encodeActionW`) and the canonical Rust enums
  (`cell/src/program.rs`), cross-checked against `wasm/src/bindings.rs`. Byte-stable.
  **This is the single best asset in the whole frontend** and it is currently surfaced
  by exactly two inspectors (`ontology.js`, `predicate-explorer.js`) buried inside the
  Starbridge tool barrel.
- **Distributed protocols are now machine-checked in Lean** (read-only, names only):
  `Dregg2/Distributed/{BlocklaceFinality, MembershipSafety, LaceMerge, Consensus,
  FinalityGate, StrandIntegrity, EntangledJoint, CellMigration, Revocation}.lean` and
  `Dregg2/Exec/{CapTPHandoffSound, CapTPConcrete, CapTPGCConcrete, CapTPConsentLace,
  CapTPSettlement, CapTPConfinement}.lean`. The paper and the site still describe these
  as "tests under simulated network conditions" / Silver-Vision say-so. **Stale.**
- **The ONE-circuit migration is in flight** (tasks #36–#49, `EffectVmEmit*`): the goal
  is to collapse hand-written AIRs A/B/C into a single descriptor-driven circuit emitted
  from Lean. The paper still cites "~151 columns after Stage 7-γ.0 + γ.2 Phase 1" and
  "Kimchi/Pickles as a credible alternative outer layer" as the present tense. That is
  the OLD architecture. **Stale / needs a forward-looking rewrite, carefully — I do not
  own the circuit so the plan flags the claims rather than inventing new numbers.**
- **Live devnet** `devnet.dregg.fg-goose.online`: `/status` → `healthy:true,
  dag_height:30341, block_count:30341, consensus_live:true, federation_mode:"solo",
  note_count:0`. So consensus is producing blocks but **the ledger is empty**
  (`/api/cells` → `[]`). `/health` and `/turns/encryption-key` are 200.
  **`/api/node/producer`, `/api/node/identity`, `/api/blocklace/checkpoint`,
  `/api/receipts`, `/api/federations` are all 404/empty on the deployed node** — the
  binary in `node/src/api.rs` has these routes, but the DEPLOYED build predates them.
  Honest consequence: any explorer/IDE that grounds on the producer-status surface must
  degrade gracefully (these are the truth surfaces; they aren't live yet → see §6).
- **Node turn-submit reality:** `/turn/submit` (`SubmitTurnRequest`/`TurnActionSpec`/
  `TurnEffectSpec`, `node/src/api.rs:216–253`) is the server-signed path and accepts
  **only 4 effect kinds** — `SetField, Transfer, EmitEvent, IncrementNonce`. The richer
  `/turns/submit` path takes a fully SDK-built `SignedTurn`. The wasm `execute_turn`
  (`wasm/src/bindings.rs:453`) runs the **full** executor in-browser. So: the in-browser
  runtime can *simulate* all 56 effects, but *submitting* to a real node is currently a
  4-effect server-signed path or a SignedTurn the browser cannot yet build (no JS-side
  Ed25519 turn signing — `studio.html` itself notes "Next: JS-side signing"). **This is
  the load-bearing gap for the whole compose→submit story.**

What is genuinely SHIPPED on the web today:

- `site/src/*.html`: index (371 L), apps (213), learn (92), paper (145), demo (97),
  docs (11 — a stub), playground.html (841 — note: the *real* playground is the separate
  `site/playground/` tree), starbridge (206).
- `site/playground/` — 31 demo sections + 10 visualizers, its own bespoke index (275 L).
- `site/explorer/` — a read-only network explorer (222 L), 11 panels.
- Studio / Starbridge: `site/src/_includes/studio/` — 43 inspector custom elements,
  a 2343-line `starbridge.js` orchestrator, three runtimes (`in-memory` 820 L wasm sim,
  `remote` 841 L read-only node poller, `extension` 236 L), a predicate-explorer with a
  faithful JS mirror of the locally-evaluable constraint fragment.
- `extension/` — MV3 browser wallet (provision/recovery/disclosure-picker/confirm-intent/
  share-capability), ships `dregg_wasm` (5.2 MB), TS `src/`.
- `discord-bot/` — Rust bot (presence, activity_feed, discord_caps, embeds, http_server).
- `app-framework/src/webgen.rs` — the anti-drift JS-constants generator (`ConstantsModule`
  → `constants.generated.js` + `assert_matches_file` drift test). The PATTERN we extend.

---

## 1. Diagnosis: why Starbridge is "cool but overwhelming / not a helpful IDE"

I read `site/src/starbridge.html` + `starbridge.js`. The problem is structural, not cosmetic.

**1a. It is an inspector browser cosplaying as an IDE.** The left "System Map" pane stacks
**ten** always-visible sections at once (Apps, Scripts, Cells, Receipts, Intents,
Capabilities, Federations, Blocks, Activity, Outbox). The center pane is a generic URI
inspector. The right pane is a Raw-JSON / Console / Activity tri-tab. Plus a top URI bar,
a time scrubber, a command palette, Snapshot, Map-toggle, Tools-toggle, Back/Forward, and
a surface strip (Workbench/Apps/Activity/Playground/Explorer). **There is no task. Every
affordance is presented with equal weight at all times.** A newcomer cannot tell what they
are *supposed to do here*. That is the overwhelm.

**1b. There is no authoring loop.** Searching `starbridge.js` for compose / validate /
simulate / submit / buildTurn: the only "turn" is a hardcoded demo transfer
(`[{type:'transfer', to: bob, amount:100, excess:500}]`, line ~1816) wired to a "Run
transfer turn" button. The console verbs are `help/seed/transfer/turn/fed/intent/app/
inspect/raw/snapshot/runtime/clear` — a demo driver, not an editor. You cannot author a
cell program, write a predicate, assemble an arbitrary turn, see why it would be rejected,
or submit it. The `predicate-explorer` (the one real authoring surface) is registered deep
in the inspector barrel and not foregrounded as a first-class workflow.

**1c. Three overlapping interactive surfaces with no division of labor.** Playground (31
demo sections), Starbridge (inspector IDE), Explorer (network browser) all overlap. The
nav lists Starbridge, Explorer, AND Playground as peers. Playground re-implements its own
seeded in-memory runtime + embeds the same `<dregg-*>` inspectors. Three doors, no map of
which door is for which job. **This is the deepest cause of "overwhelming": the product
has not decided what each surface is FOR.**

**1d. Read-only remote.** `runtime-remote.js` exposes `executeTurn: notPermitted(...)`.
Connect Starbridge to the live node and you can *look* but never *do*. The only runtime
that can act is the in-browser sim. So the "IDE" can't drive the real system.

**1e. Honest-but-buried model fidelity.** The good stuff — predicate JS mirror labels
which constraints are `locally_evaluable` vs "needs executor"; the ontology catalog is
drift-guarded; the in-memory peer-exchange demo drives the real `dregg_cell::PeerExchange`
— is all real and all hidden behind chrome.

---

## 2. The reframe: three surfaces, three jobs

Stop treating Playground / Starbridge / Explorer as peers. Assign each a single job and a
single audience. Collapse duplication into shared studio components.

| Surface | One job | Audience | Runtime |
|---|---|---|---|
| **Learn / Ontology** (`/learn/ontology`, paper) | *Understand* the 56 effects, 29 constraints, the verified guarantees | first contact | none (catalogs) |
| **Studio (was Starbridge)** | *Author* a cell program / predicate / turn → validate → simulate → (submit) | builder | in-memory wasm primary; remote for submit |
| **Explorer** | *Observe* a real node / the live mesh | operator / auditor | remote (read-only) + in-browser node |
| ~~Playground~~ | **demoted to a gallery** of worked examples that deep-link INTO Studio | curious | (links) |

Playground's 31 sections become **example seeds** ("open this in Studio") rather than 31
bespoke mini-apps. This deletes the third door without deleting the content.

---

## 3. The authoring IDE Studio actually needs (compose → validate → simulate → submit)

This is the heart of the request. A real cell-program / predicate / caveat authoring IDE
is a **four-stage pipeline made visible as the primary surface**, not a side panel.

### Stage COMPOSE — build the thing from the verified vocabulary
- **Cell-program / predicate composer.** Pick `CellProgram` kind (4) → add
  `StateConstraint`s from the 29-variant palette (typed fields, one-line semantics, all
  from `predicate-catalog.generated.json`) → add `TransitionGuard`s (6). The palette is
  the ontology catalog; it cannot drift. Already 80% present inside
  `predicate-explorer.js` — **promote it from inspector to top-level pane.**
- **Turn composer.** Pick effects from the 56-effect palette (grouped by the 11 catalog
  categories: value/state/authority/lifecycle/escrow/privacy/seal/bridge/queue/swiss/other),
  fill typed args, see the required authorization facet (write/grant/control) per effect
  inline. Catalog already carries `facet` + `args` + `category` per effect.
- **Caveat / attenuation builder.** Compose a `CapabilityCaveat` chain; show monotone
  attenuation (granted ≤ held) as you narrow it.

### Stage VALIDATE — explain accept/reject BEFORE running
- Run the composed predicate against an `(old → new)` 8-slot state and show per-constraint
  pass/fail with the human-readable `why` (the JS mirror already does this for the 15
  locally-evaluable constraints). For the 14 that need the executor, label them honestly
  "needs executor — will check in Simulate" (NOT faked). This honest split is already in
  the catalog (`locally_evaluable`) — surface it.
- Static turn lint: missing facet for an effect, attenuation that grows authority, a
  transfer that violates conservation (the in-memory demo already knows `excess`), an
  effect not in the node's 4-effect submit set (warn it's sim-only).

### Stage SIMULATE — run the real executor in the browser
- Execute the composed turn through the wasm `DreggRuntime` (`execute_turn` runs the FULL
  56-effect executor — this is the strongest card we hold). Show the state diff
  (`visualizers/state-diff.js` exists), the receipt, the post-state commitment, and — for
  predicate-bearing turns — which constraints the executor actually enforced.
- `execute_turn_step_by_step` (`wasm/src/bindings.rs:478`) already exists → a real
  **step debugger** (`turn-debugger.js` inspector exists; wire it to the composer output).

### Stage SUBMIT — push to a real node (honest about the gap)
- Two truthful paths today:
  1. **Server-signed `/turn/submit`** — works NOW for `SetField/Transfer/EmitEvent/
     IncrementNonce` only. Good enough for a first real-submit demo on devnet (once the
     ledger is seeded). Studio must gate the Submit button to those 4 and say so.
  2. **SignedTurn `/turns/submit`** — full effect set, but needs **JS/wasm-side turn
     signing**, which does not exist yet (the in-memory runtime signs internally with
     deterministic sim keys via `AgentCipherclerk::sign_action`; there is no path to sign
     a turn with a USER key from the browser/extension). The **extension** is the natural
     signer (it already holds keys, does `confirm-intent`/`disclosure-picker`). Studio →
     extension `signTurn` → `/turns/submit` is the real architecture. The
     `runtime-extension.js` adapter and `appApiRows` already anticipate a `signTurn`/
     `signTurnV3` method — it is referenced but not implemented end-to-end.

**Honest bar:** Compose/Validate/Simulate can be 100% real and offline TODAY (wasm + the
drift-guarded catalogs). Submit is partial: 4-effect server-signed is real; full-effect
user-signed needs the extension-signer leg. The plan does not pretend otherwise.

---

## 4. What a real-usecase Explorer needs

The current explorer is 11 generic panels. A *usecase* explorer answers operator/auditor
questions:

- **"Is this node running the verified producer?"** → `/api/node/producer`
  (`state_producer`, `lean_producer_enabled`, `full_turn_proving`, `covered_effects` vs
  `uncovered_effects`, `summary`). This is THE honesty surface of THE SWAP. Make it the
  explorer's hero panel. **Caveat: 404 on the deployed node today → show "node predates
  this endpoint" rather than blank.**
- **"Who am I / what cell do I act on?"** → `/api/node/identity` (operator pubkey, agent
  cell, balance, nonce). Also 404 on deployed today.
- **Verified-guarantee badges.** For each thing the explorer shows (a finalized block, a
  handoff certificate, a membership change), link to the Lean theorem that backs it
  (BlocklaceFinality / CapTPHandoffSound / MembershipSafety). Not "trust us" — "here is
  the machine-checked statement." This is the single biggest credibility upgrade available
  and it is currently absent everywhere on the site.
- **Receipt → witness drill-down** already exists in `runtime-remote.js`
  (`/api/receipts/{hash}/witnesses`); foreground it with proof_status.
- **Live blocklace DAG** via `/api/blocklace/blocks` + `<dregg-block-dag>` (real wasm-backed
  view; the JS `Math.random` consensus sim was already removed — good).

---

## 5. In-browser node (participating in the real mesh)

There is a **Lean-in-wasm POC** referenced in the brief and a 5.2 MB `dregg_wasm` already
shipping in `extension/` and `site/pkg/`. The in-browser `DreggRuntime` already: creates
cells, runs the full 56-effect executor, signs internally, drives `PeerExchange`
(sign/verify signed `PeerStateTransition`s — the Discord-paste UX). What it does NOT do:
gossip on the real blocklace, sync the DAG, or submit user-signed turns.

The realistic ladder (each rung is a shippable, honest milestone):
1. **Read-only mirror node** (today, almost): poll `/api/blocklace/blocks` + `/checkpoint`,
   verify the BLS quorum certificate client-side, render the DAG. "Your browser
   independently verified finality." (Needs the deployed node to expose those endpoints —
   currently 404.)
2. **PeerExchange participant** (today, real): two browsers exchange signed transitions out
   of band (the existing copy/paste UX), promotable to federation order on reconnect. This
   already works against `dregg_cell::PeerExchange`. **Foreground it as the in-browser
   node's first real superpower** — it is the most honest "you are in the mesh" story we
   can tell right now.
3. **Submitting participant**: extension-signed turns → `/turns/submit` (the §3 SUBMIT leg).
4. **Gossiping node** (research): wasm node that ingests/relays blocks over a WS/relay
   bridge. The node has `/ws`, `gossip.rs`, `relay_service.rs` — the bridge exists
   server-side; the browser side is unbuilt. Keep this honestly labeled "experimental."

---

## 6. Paper: stale claims to fix (paper/ is in-lane)

Concrete edits (NO fabricated numbers; where I don't own the source I FLAG, not invent):

- **"21+ variant `StateConstraint`"** appears in `01-introduction.typ` (×2),
  `03-authorization.typ` (heading "§ `StateConstraint`: 21+ variants" + caption),
  `08-storage.typ` (×4), `19-conclusion.typ`, `15-implementation.typ`. The drift-guarded
  catalog says **29**. Update to "29-variant" and cite the generator as the source of
  truth (it parses `cell/src/program.rs`). This is a safe, grounded number.
- **"~151 columns after Stage 7-γ.0 + γ.2 Phase 1"** in `01-introduction.typ` (×2),
  `04-proofs.typ:493`, `19-conclusion.typ:38`, `15-implementation.typ:24`. The ONE-circuit
  migration (tasks #36–#49) is collapsing the hand-AIRs. **DO NOT invent a new column
  count.** Replace the present-tense pin with a forward-honest sentence: the circuit is
  migrating to a single descriptor-driven AIR emitted from the verified Lean executor;
  cite that the descriptor↔hand-AIR differential is the live gate (read-only: this is the
  state of #53). Coordinate the exact wording with the circuit workflow before committing
  the paper edit — flag in the plan, do not unilaterally rewrite circuit claims.
- **Distributed protocols described as tests, not proofs.** `06-fabric.typ`,
  `15-implementation.typ:132` ("Consensus correctness tests under simulated network
  conditions"), `02-model.typ`. These guarantees are now **machine-checked in Lean**
  (`Dregg2/Distributed/*`, `Dregg2/Exec/CapTP*`). Add a formal-verification subsection (or
  extend `16-formal-verification.typ`) that names the verified theorems: blocklace finality,
  membership safety, lace-merge, CapTP handoff soundness/unforgeability, GC concreteness,
  consent-lace, entangled joint turns. This is the paper's biggest understatement.
- **"Silver is what the runtime actually delivers today"** (`01-introduction.typ`) — the
  Silver/Golden framing predates the verified distributed layer + the Lean producer on the
  commit path. Revisit the two-visions section so it reflects that the kernel constraint
  family is now Lean-checked, not executor's-say-so, for the distributed protocols.

---

## 7. Prioritized roadmap (Build phase)

Ordered by **value ÷ honesty-risk**. P0 items are real-today with zero overclaim.

- **P0-A — Foreground the ontology + predicate composer as a first-class page.** The
  drift-guarded catalogs are the crown jewel and they're buried. Cheapest highest-value
  move. (§1e, §3 COMPOSE/VALIDATE)
- **P0-B — Studio shell redesign: task-first, not pane-first.** Replace the always-on
  10-section sidebar with a mode switch: **Author / Simulate / Observe**. Collapse the tri-
  tab + scrubber + palette behind progressive disclosure. (§1a–§1c)
- **P0-C — Paper de-stale: 29 constraints + verified-distributed subsection.** Safe,
  grounded, big credibility. Defer the circuit-column rewrite to coordinate. (§6)
- **P1-A — Compose→Validate→Simulate loop wired end-to-end in Studio** on the in-memory
  wasm runtime (full 56 effects, step debugger, state diff). 100% real offline. (§3)
- **P1-B — Explorer usecase panels:** producer-status hero + verified-guarantee badges +
  receipt/witness drill-down, all degrading gracefully on the older deployed node. (§4)
- **P1-C — Demote Playground to an example gallery that deep-links into Studio.** Delete
  the third door; keep the content as seeds. (§2)
- **P2-A — SUBMIT leg:** wire the 4-effect server-signed `/turn/submit` from Studio (gated
  + labeled), and design the extension-signer → `/turns/submit` path for full effects. (§3)
- **P2-B — In-browser node ladder rungs 1–2:** client-side finality verification + the
  PeerExchange "you're in the mesh" surface as a real feature. (§5)
- **P3 — Deploy the newer node** so `/api/node/producer`, `/api/node/identity`,
  `/api/blocklace/*`, `/api/receipts` exist on devnet (this is task #26, not strictly
  in-lane, but P1-B is blocked on it for live data — flag the dependency).

---

## 8. File-level work breakdown (for the Build phase)

All paths in-lane unless flagged. Each item names the files to touch and why.

### P0-A — Ontology + predicate composer page
- NEW `site/src/learn/ontology.html` already exists (94 L) — audit it; likely thin. Make it
  the canonical effect-catalog browser using `<dregg-ontology>` (`inspectors/ontology.js`)
  + `<dregg-predicate-explorer>` (`inspectors/predicate-explorer.js`).
- `site/src/_includes/studio/inspectors/predicate-explorer.js` — extract the composer half
  into a reusable component the Studio Author mode also mounts (avoid a second copy).
- `site/src/_includes/nav.html` — add "Ontology" / fold "Learn" to point here.
- Keep `site/tools/gen-ontology-catalog.js` as the source; run `--check` in CI/build.

### P0-B — Studio shell redesign
- `site/src/starbridge.html` — replace the 10-section `<aside>` with a 3-mode shell
  (Author / Simulate / Observe). Move scrubber/palette/snapshot behind a "more" disclosure.
  Consider renaming the page Studio (the nav already says "Starbridge" → align naming).
- `site/src/_includes/studio/starbridge.js` (2343 L) — split the surface-switch logic into
  mode controllers; the inspector-router stays, the always-on section list goes. This is
  the big refactor; do it incrementally behind the mode switch.
- `site/src/_includes/studio/starbridge.css` — restyle for task-focus (one primary pane).

### P0-C — Paper de-stale (safe subset)
- `paper/sections/03-authorization.typ` — "21+ variants" → "29 variants"; fix heading +
  caption; cite `gen-ontology-catalog.js`.
- `paper/sections/01-introduction.typ`, `08-storage.typ`, `19-conclusion.typ`,
  `15-implementation.typ` — same 21→29 update everywhere it appears.
- `paper/sections/16-formal-verification.typ` — add the verified-distributed-protocols
  subsection (names from `Dregg2/Distributed/*`, `Dregg2/Exec/CapTP*`). Read those Lean
  files READ-ONLY for the exact theorem statements before writing prose.
- Rebuild: `typst compile paper/main.typ` (or `paper/dregg.typ`) in Docker; verify PDF.
- DEFER (flag, coordinate): the "~151 columns" rewrite in `04-proofs.typ`,
  `01-introduction.typ`, `19-conclusion.typ`, `15-implementation.typ`.

### P1-A — Compose→Validate→Simulate loop
- NEW `site/src/_includes/studio/compose/turn-composer.js` — 56-effect palette from
  `ontology-catalog.generated.json`, typed-arg forms, inline facet badge, conservation lint.
- NEW `site/src/_includes/studio/compose/program-composer.js` — reuses the P0-A composer.
- `site/src/_includes/studio/runtime-in-memory.js` — expose a clean `simulateTurn(actions)`
  that returns {diff, receipt, commitment, enforcedConstraints}; already has `executeTurn`.
- `site/src/_includes/studio/inspectors/turn-debugger.js` — wire to
  `execute_turn_step_by_step` for the step view.
- `site/playground/visualizers/state-diff.js` — reuse for the diff render (move to studio/).

### P1-B — Explorer usecase panels
- `site/explorer/index.html` + its `api.js` — add a producer-status hero panel
  (`/api/node/producer`) and identity panel (`/api/node/identity`) with graceful 404
  fallback ("node predates this endpoint").
- NEW `site/src/_includes/studio/inspectors/guarantee-badge.js` — a `<dregg-guarantee>`
  element mapping a surface (finalized block / handoff cert / membership change) to its
  Lean theorem name + a one-line plain-English statement.
- `site/src/_includes/studio/runtime-remote.js` — already polls receipts/witnesses; expose
  producer-status + identity to the explorer.

### P1-C — Playground → gallery
- `site/playground/index.html` — convert the 31-section nav into example cards, each with
  an "Open in Studio" deep-link (`?seed=<name>`). Keep heavy sections (proofs, circuit) as
  standalone for now; migrate the rest to seeds.
- `site/src/_includes/nav.html` — Playground becomes "Examples" (or drop from top nav).

### P2-A — Submit leg
- `site/src/_includes/studio/runtime-remote.js` — implement `submitTurn` for the 4
  server-signed effect kinds via `POST /turn/submit` (`SubmitTurnRequest` shape from
  `node/src/api.rs:216`). Gate + label "server-signed; 4 effects only."
- `extension/src/api.ts` + `extension/src/page.ts` — design `signTurn(turn)` → SignedTurn
  for the full-effect `/turns/submit` path (extension holds the user key). This is the
  honest path to user-signed submission; scope it as a P2 design spike, not a claim.
- `site/src/_includes/studio/runtime-extension.js` — wire `signTurn` through (the adapter
  already references the method name).

### P2-B — In-browser node rungs
- NEW `site/src/_includes/studio/node/finality-verify.js` — fetch `/api/blocklace/checkpoint`
  + blocks, verify the BLS quorum cert in wasm, render "browser-verified finality."
- Foreground the existing PeerExchange UX (`studio.html` lines 76–98 + the wasm
  `create_peer_transition`/`verify_peer_transition`) as a named Studio feature, not a
  "spike findings" footnote.

### Cross-cutting — keep the anti-drift discipline
- Extend the `app-framework/src/webgen.rs` `ConstantsModule` pattern: any new
  studio-side constant set (effect categories, facet legend, theorem→surface map) gets a
  generator + `--check` so it can't drift. Mirror `gen-ontology-catalog.js`'s `--check`.

---

## 9. Honest scorecard (real vs rough)

| Capability | State |
|---|---|
| Ontology/predicate catalogs, drift-guarded | **REAL** (`--check` EXIT 0, 56/29) |
| In-browser full-executor simulation | **REAL** (wasm `execute_turn`, all 56) |
| Predicate validate w/ honest evaluable-split | **REAL** (15/29 mirrored, 14 labeled) |
| PeerExchange browser↔browser | **REAL** (drives `dregg_cell::PeerExchange`) |
| Studio as an authoring IDE | **ROUGH** (inspector browser; no compose loop) |
| Submit to real node | **PARTIAL** (4-effect server-signed; full-effect user-signed unbuilt) |
| Explorer producer-status / identity | **BLOCKED** (endpoints 404 on deployed node) |
| Verified-distributed guarantees on site/paper | **ABSENT** (proven in Lean, not surfaced) |
| In-browser gossiping node | **EXPERIMENTAL/unbuilt** (server bridge exists) |
| Paper numbers | **STALE** (21→29 safe; 151-cols needs coordination) |

The frontend's problem is not capability — the wasm executor + drift-guarded catalogs are a
strong, honest foundation. The problem is **product framing**: three undifferentiated doors,
an inspector-browser mislabeled as an IDE, and the most credible assets (verified guarantees,
the producer-status honesty surface) buried or unsurfaced. The overhaul is mostly
**re-foregrounding what's already real** + building the one missing thing (the compose loop)
+ telling the truth the Lean proofs now license us to tell.

— a little verse for the road —
_ten panes shouting, none of them ask /
"friend, what are you here to do?" —_
_collapse the chrome to a single task,_
_let the proof speak, and let the cell come through._  ( ˘▾˘ )
