# Starbridge, Reimagined: Lean4 as a Full-Fledged Web Citizen

**Status:** program-of-record + living tracker. Started 2026-06-02. Supersedes the
wasm-bindgen substrate rule of `docs-old/STARBRIDGE-PLAN.md` §1. Builds on
`HATCHERY.md` (the verification toolkit) and the dregg2 metatheory.

> **Governing constraint (ember, non-negotiable):** *we never, ever have a
> placeholder in the frontend again.* The old Starbridge's `§5` was a graveyard of
> "BLOCKED ON HUMAN / awaiting wasm32 support for X." That pattern is **forbidden**.
> Every surface element is backed by a real Lean term, proof, or executor result —
> or it does not ship.

---

## 0. The hinge

The old Starbridge was a **viewer onto an opaque runtime**: a browser IDE piping
canonical Rust through wasm-bindgen, with the actual verification living in two
worlds it could not touch (the `circuit/` STARKs and the Lean metatheory — the
latter *entirely absent* from the browser). Trust was a *badge attached to a
receipt*: "there's a STARK somewhere, trust us." The browser never checked anything.

Embedding the Lean4 runtime flips the polarity:

> **The verification machinery itself comes to the browser. dregg2 is no longer a
> theory that lives elsewhere — it is the runnable executor, the checkable kernel,
> and the authorable metaprogram, all hosted in the page. Starbridge stops being a
> window onto a verified-elsewhere system and becomes the verification surface.**

This is the fusion of two things we built from opposite ends:
- **The Hatchery** — the verification *logic*: `livingCellA_carries` + `CellContract`
  + `exec_frame` + the shape catalog. (`HATCHERY.md`.)
- **Starbridge** — the verification *surface*.

They were always the same project. The new Starbridge is the Hatchery's delivery
vehicle, and "use dregg with assurance" becomes literal: the user's own browser
re-checks the proof.

---

## 1. Confirmed ground truth (2026-06-02)

Not aspirational — verified against the live tree this session:

| Fact | Evidence |
|---|---|
| `emcc` (Emscripten 5.0.1) installed | `/opt/homebrew/bin/emcc` |
| Lean→C→static-archive pipeline works | `dregg-lean-ffi/libdregg_lean.a` = whole closure via `leanc -c` + `ar` |
| The verified executor is already `@[export]`ed | `Exec/FFI.lean`: `dregg_exec_full_forest_auth`, `dregg_exec_full_turn_wide`, `dregg_record_kernel_step_caps` |
| The Lean runtime link recipe is known | `dregg-lean-ffi/build.rs`: `leancpp/Init/Std/Lean/leanrt/Lake/gmp/uv` + libc++ |
| Lean has an official Emscripten build | runs under Node; browser-as-library WIP (leanprover Zulip) |
| ProofWidgets fully present | `GraphDisplay`, `Recharts`, `InteractiveSvg`, `HtmlDisplay`, `OfRpcMethod`, `PenroseDiagram`, `Panel` |
| `livingCellA_carries` is real | `Exec/CellCarry.lean` — the "prove one step, get forever free" coalgebra |
| Build is green & current | `.lake/build/lib/lean/Dregg2.olean` present (last-known 3455 jobs, 0 sorry) |

**What the spike must still establish (the one honest unknown):** the Lean *runtime*
(`leancpp/leanrt/gmp/uv`) built for `wasm32-emscripten`, and the **weight** of the
gc-sectioned executor blob. Everything branches on that number.

---

## 2. The A/B/C ladder (independently shippable rungs)

**Rung A — the verified executor in the browser (highest certainty; do first).**
Retarget the existing FFI C-export pipeline to `wasm32-emscripten` via `emcc`. The
old `InMemoryRuntime` (wasm-bindgen'd `dregg_turn::TurnExecutor`) is *replaced by the
proved Lean term* `dregg_exec_full_forest_auth`. A turn no longer returns just a
state — it returns a state **plus its `cexec_attests` proof of all four StepInv
conjuncts**, and per-step proofs link into the proof-carrying forest in-page. This is
**THE SWAP landing in the browser first** (the ideal low-stakes proving ground, where
the differential ratchet runs visibly).

**Rung B — the kernel in the browser (the assurance keystone).**
Ship the Lean *kernel* (proof checker — small, portable; the thing the axiom-clean
TCB claim rests on). The browser receives a `CellContract.forever` proof term and
**re-checks it locally**. `#print axioms` runs in the page → `[propext,
Classical.choice, Quot.sound]`, the entire trust base, verified on the user's
machine. The difference between "the website says it's verified" and "my browser
checked the proof."

**Rung C — the elaborator in the browser (the reflective / metaprogrammable dream).**
Ship the full elaborator + a **trimmed** Dregg2 olean closure. The user authors a
cell-program in the eDSL (`dregg_effect`/`dregg_choreo`), declares an invariant via a
Hatchery shape macro (`monotone_registry%`, `conservation%`), and **watches the
metaprogram run live** — sees `exec_frame` kill the 45 boring arms and hand back the
one real obligation, edits, re-checks. Heaviest (oleans), but it's an engineering
problem upstream already solved (lean4web / the playground), not research.

ember's directive is **all three**, heavy is fine. B gives ~80% of the assurance
value at a fraction of C's weight; A is the certain near-term win and advances the
SWAP. We climb A→B→C, but build them as independent rungs.

---

## 3. The four pillars

### Pillar 1 — SUBSTRATE (`web/` + toolchain): Lean→WASM hosting
- **1A** Rung-A spike: trivial `@[export]` → wasm via emcc under Node; then scale to
  `dregg_exec_full_forest_auth`. Measure with `--gc-sections`/LTO.
- **1B** Rung-B: Lean kernel → wasm, proof-term re-checking + in-page `#print axioms`.
- **1C** Rung-C: elaborator + trimmed oleans; olean load/cache strategy; WebWorker host.
- **Packaging**: emcc flags, JS glue, WebWorker, olean delivery.

### Pillar 2 — THE HATCHERY (`Dregg2/Verify/`, pure Lean): HATCHERY.md H1–H4
- `Verify/Tactics.lean` — `carry_forever`, `exec_frame`, `crypto_portal` (Tier 1).
- `Verify/Aesop.lean` — the `dregg` aesop rule-set + `@[dregg_frame/_bridge/_grow]` (Tier 2).
- `Verify/Contract.lean` — `CellContract` + `forever`/`always` (Tier 3).
- `Verify/Catalog.lean` — `monotone_registry%` / `conservation%` / `confinement%` /
  `automaton_inv%` (Tier 4).
- Regression: Identity / NameService / Subscription re-expressed as `CellContract`s,
  theorems regression-equal to the hand proofs.

### Pillar 3 — WIDGET VOCABULARY (`Dregg2/Widget/`, pure Lean + ProofWidgets)
The old `<dregg-X>` JS web components, reborn as ProofWidgets driven by Lean RPC over
the **actual Lean term**:
- `Widget/DreggForest.lean` — call-forest off the `FullForestA` value (GraphDisplay).
- `Widget/ConservationLedger.lean` — per-asset `bal : CellId→AssetId→ℤ` deltas (Recharts),
  with `recKExecAsset_conserves_per_asset` attached as a hoverable, kernel-backed badge.
- `Widget/CapabilityGraph.lean` — Granovetter graph (InteractiveSvg), `granted ≤ held`
  non-amplification clickable.
- `Widget/ProofBadge.lean` — **trust-tier-as-proof-fact**: tier = does the kernel accept
  `forever` + what `#print axioms` costs (NOT "is a STARK attached"). `Placeholder`
  becomes the honest-and-rare "no Lean term yet."
- `Widget/ContractView.lean` — a `CellContract` rendered: invariant, shape, one-step
  obligation, the `forever` theorem.
- Testable in the editor InfoView **now**, before any browser hosting.

### Pillar 4 — THE SURFACE (`site/` + `web/`): the host
- Standalone host page: in-browser Lean (A/B/C) + the widget vocabulary + eDSL authoring
  + live kernel-checking.
- Reborn `dregg://` URIs, inspector mounts, activity feed — every one backed by Lean.
- Hybrid bridges to the existing site/extension: **Lean owns verification; Rust owns the
  I/O / crypto / network periphery** (the 8 `@[extern]` primitives stay Rust, out of TCB).
  Single-machine browser node = the degenerate distributed system where the strong
  properties hold (dregg4 single-machine principle) — the ideal place to run the full
  verified executor locally and check the proofs locally.

---

## 4. Dependency graph & execution order

```
Pillar 2 (Hatchery)   ─┐  pure Lean, buildable NOW, independent of substrate
Pillar 3 (Widgets)    ─┤  pure Lean + ProofWidgets, testable in InfoView NOW
                       │
Pillar 1 (Substrate)  ─┤  gating empirical; driven in background, in parallel
                       │
Pillar 4 (Surface)    ─┘  integrates 1+2+3 — comes after they have real artifacts
```

Pillars 2 & 3 fan out **wide immediately** (file-disjoint new modules — the proven
swarm-safe pattern; no worktrees, shared olean cache). Pillar 1 is the gating spike,
driven empirically in the background. Pillar 4 integrates last.

**Verify-don't-trust discipline (carried from every prior wave):** `#assert_axioms`
certifies kernel-clean, *never* faithful/non-vacuous. Every agent-produced module gets
MY gate — build green + read the load-bearing bodies for vacuity + `#assert_axioms`
clean — before it's trusted. No self-reports.

---

## 5. What "no placeholder" operationally means

The old trust-tier UX (`Placeholder | Silver | Golden`) was cosmetic — "is a proof
attached?" The reborn tier is a **fact about the proof term**, computed live:

- **Kernel-checked** — the browser's Lean kernel accepts the `forever` term; `#print
  axioms` shows only `[propext, Classical.choice, Quot.sound]`.
- **Carrier-bounded** — accepts modulo a named §8 crypto carrier (the 8 `@[extern]`
  primitives), surfaced explicitly, never hidden.
- **No term yet** — the rare, honest "this hasn't been verified" — and it is *visibly*
  unverified, never dressed as anything else.

There is no "MockProofVerifier renders differently" anymore. There is no mock.

---

## 6. Prior art (adopt, don't reinvent)
- Lean official Emscripten build (Node today, browser-as-library WIP) — Rungs B/C base.
- `leanprover-community/lean4web` — the in-browser InfoView + WebWorker Lean pattern.
- `live.lean-lang.org` — the playground.
- ProofWidgets4 (`Html`/`Jsx`/`OfRpcMethod`/`GraphDisplay`/`Recharts`/`InteractiveSvg`).
- T-Brick `lean2wasm` — Lean→wasm tooling reference.

---

## 8. Pillar 4 architecture — the hybrid surface (grounded)

The old surface (`site/src/_includes/studio/`) is a **signal-based `Runtime` interface**
+ a **`<dregg-X>` inspector vocabulary** + a **three-pane shell** (`starbridge.html`).
We keep the seams that are good and replace the layers that were the wasm-straw ceiling.

**The Runtime seam (keep the shape, swap the backend).** `runtime-in-memory.js` exposes
`getCell(id)` / `listCells()` / `listReceipts()` / `getReceipt(hash)` /
`listCapabilities(agentIdx)` — each a Preact signal that re-fetches on a `version` bump;
mutations bump `version`; `CAPS = {read, mutate, debug, timeTravel}`. The new
**`RuntimeLean`** implements the *same* interface, backed by the in-browser **verified Lean
executor** (Rung A `dregg_exec_full_forest_auth`) instead of wasm-bindgen'd Rust:
- `getCell(id)` → a state-query export over the live `RecordKernelState`.
- a turn mutation → `dregg_exec_full_forest_auth`, whose result **carries its
  `cexec_attests` attestation**; per-step proofs link into the proof-carrying forest.
- `CAPS.timeTravel` becomes real (checkpoint/replay are proved runtime theorems —
  `CellRuntime`), not the old `false` placeholder.

The shell (`starbridge.html` three-pane, URI bar, runtime picker, palette) is adapted, not
rebuilt. The runtime picker gains **In-browser (Lean)** beside the retired wasm-bindgen one.

**The inspector layer (replace, don't feed).** The hand-written JS `<dregg-X>` web
components are *superseded* by the **Lean-authored ProofWidgets** of Pillar 3 — this is the
substrate-rule resolution: rendering is now Lean, not a JS reimplementation. We host them by
adopting the upstream **InfoView stack**:
- In-browser Lean runs in a **WebWorker** (the lean4web pattern).
- The panel React app embeds `@leanprover/infoview` + speaks the InfoView **RPC protocol**
  (`@[server_rpc_method]`) to the worker — the same channel ProofWidgets already use.
- A dregg panel = `<DreggForest>` / `<ConservationLedger>` / `<CapabilityGraph>` /
  `<ProofBadge>` driven by `RuntimeLean` state over RPC.

**The hybrid boundary (what stays Rust).** Lean owns *verification + turn-logic + rendering*.
Rust (via the existing wasm or a node) owns the *I/O / crypto / network periphery*: the 8
`@[extern]` primitives, gossip/consensus dissemination, persistence. The single-machine
browser node is the degenerate distributed system where the strong properties hold (dregg4
single-machine principle) — the ideal place to run the full verified executor + check proofs
locally.

**Three rungs, three assurance levels, one surface:**
| Surface capability | Needs | Rung |
|---|---|---|
| Inspect/execute real verified turns + attestation | executor wasm + `RuntimeLean` | A |
| In-page "this theorem holds" re-checked locally (`#print axioms`) | kernel wasm | B |
| Author a cell-program + watch `exec_frame` discharge it live | elaborator + trimmed oleans + Hatchery | C |

## 8b. Rung C — the live authoring loop (the metaprogrammable dream)

The authoring vocabulary already exists in-tree; Rung C is the *surface* that runs it live:
- **`dregg_effect`** (`Dregg2/DSLEffect.lean`) — declare an effect; elaborates to a
  `CatalogEffects` `LinearityClass` coloring (`Conservative/Monotonic/Terminal/Generative/
  Annihilative/Neutral`).
- **`dregg_choreo { A ~(label)~> B ; … }`** (`Dregg2/DSLChoreo.lean`) — a multiparty
  session-types block; elaborates to a verified `Coordination.GlobalType` that *inherits*
  deadlock-freedom + privacy-by-projection.
- **The Hatchery shape macros** (Pillar 2, in flight) — `monotone_registry% revoked`,
  `conservation% asset`, … — declare an invariant; expand to a `CellContract` whose one-step
  obligation `exec_frame` discharges, yielding the `forever` theorem.

**The loop** (Monaco editor → WebWorker elaborator → InfoView panels, the lean4web pattern):
1. User types a cell-program (`dregg_effect` / `dregg_choreo`) + an invariant
   (`monotone_registry% …`) in the editor.
2. The in-browser **elaborator** (Rung C) runs the macros — the user *watches the expansion*:
   the generated `CellContract`, the one-step goal, `exec_frame` killing the 45 boring arms
   and handing back the one real obligation.
3. The in-browser **kernel** (Rung B) checks the resulting `forever` term; the `<ProofBadge>`
   shows the tier from the *actual* axiom set (`Lean.collectAxioms`), live.
4. `<DreggForest>` / `<ConservationLedger>` render the program executing on the **executor**
   (Rung A) over real sample state.

All three rungs in one page: author (C), discharge + check (B), run + inspect (A). That is
"full Lean4 metaprogramming, on the web" — and there is no placeholder anywhere in the loop,
because every panel is a Lean term the user's own browser elaborated, checked, or ran.

## 9. Live tracker

(Updated as work lands. Each entry: what + gate evidence, not self-report.)

- 2026-06-02 — program opened; ground truth confirmed (§1). Launched: executor→wasm spike
  (Rung A, background); Hatchery-spine scout (**done** — verbatim spine in hand: crown at
  CellCarry.lean:57, one-step template at :135, 46-ctor `FullActionA`, `[Dregg2]` aesop set
  already declared, ProofWidgets greenfield + elaborates green); fan-out workflow
  (`Dregg2/Verify/` Hatchery pipeline + `Dregg2/Widget/` vocabulary, background). Pillar-4
  hybrid architecture drafted (§8) against the real `runtime-in-memory.js` seam.
- 2026-06-02 — **executor→wasm spike: Lean RUNS in wasm.** A Lean `@[export]`
  (`UInt64→UInt64`) compiled to WebAssembly executes under Node AND in a
  browser-library shape (ES6 `createTiny()` factory + `Module.ccall(…,"bigint",…)`),
  returning the correct result (`tiny_add(20,22)=42`; both shapes PASS, exit 0).
  Weight **~1.01 MB** wasm (`-Oz -flto --gc-sections`; ~1 MB = irreducible Lean
  runtime closure) + 61 KB JS; C-emit 0.09 s, link 1.7 s, run ~90 ms. Reproducible:
  `web/spike/build-tiny.sh`; full recipe `web/spike/RECIPE.md`. **Rung A
  (`dregg_exec_full_forest_auth`) BLOCKED by a hard ABI gap, not a flag:** the only
  prebuilt wasm Lean runtime is **v4.15.0** (official `linux_wasm32` asset dropped
  after 4.15.0 — verified absent on every release 4.16→4.30), the repo is **v4.30.0**,
  and 4.30 codegen renamed the stdlib specialization suffix `___rarg`→`___redArg`
  (proven: identical `xs++xs` → `appendTR___rarg` on 4.15 vs `appendTR___redArg` on
  4.30; v4.30 `FFI.c` references 314 `___redArg`, v4.15 runtime exports 0). **Next:**
  build a **v4.30.0 wasm Lean runtime from source** (`emconfigure cmake ../../src
  -DCMAKE_BUILD_TYPE=Emscripten -DUSE_GMP=OFF` at tag v4.30.0; 25 runtime `.cpp` +
  `doc/make/emscripten.md` confirm the path is in-tree), then re-link
  `libdregg_lean.a` with `-flto -Oz --gc-sections` (executor runtime closure ≪ the
  246 MB mathlib archive; mathlib is compile-time).
- 2026-06-02 — **launched the v4.30 wasm-Lean-runtime build from source** (background,
  the critical path): one Emscripten build of the lean4 v4.30.0 tree is the common
  substrate for ALL three rungs (its runtime libs link the executor = A; the fuller
  build is the kernel = B and elaborator = C). Staged: bank Rung A + the executor blob
  weight first, then press to B/C.
- 2026-06-02 — **Pillars 2 + 3 LANDED + GATED (my reconcile, not self-report).** The
  fan-out workflow produced 11 file-disjoint modules; `scripts/gate-starbridge.sh`
  reconcile-builds all 11 (3018 jobs, **zero sorry**; the only `sorry` hits are comments
  documenting the discipline). Bodies read for vacuity:
  - **Hatchery** (`Dregg2/Verify/{Frames,Tactics,Contract,Catalog,Regression}`):
    `exec_frame` is *honest by construction* — it splits flat so the commit goal ESCAPES
    to the caller (`skip` hand-back, never a faked close), proven by `logMono_handback_demo`
    (a trailing `exact` after `exec_frame` would error "no goals" had it faked). §5
    regressions prove statement-equality with the hand crowns *both directions*.
    `commitments_persist_via_auto` closes via the `[Dregg2]` rule-set alone while `logMono`
    hands back — so aesop is **discriminating**, not trivial. `CellContract.always` wires the
    REAL `Proof.Temporal.always_of_step_invariant` (verified it exists, not invented).
    Catalog macros expand to real `Inv` (no `Inv := True`); `confinement%` surfaces its
    `control∈U` hypothesis honestly; `automaton_inv%` is genuinely relational. Regression
    reproduces **six** shipped crowns with both-directions defeq witnesses. Axioms:
    `[propext, Quot.sound]` (subset of the triple).
  - **Widgets** (`Dregg2/Widget/{Basic,DreggForest,ConservationLedger,CapabilityGraph,
    ProofBadgeGallery,ContractView}`): every panel renders REAL data — `ConservationLedger`
    charts `((execFullForestA fma0 transferCF.1).getD fma0).kernel.bal` deltas (the ACTUAL
    committed state); `Basic.classifyAxioms` reads `Lean.collectAxioms` (the trust tier
    "cannot be faked"); provenance grep confirms real executor/axiom/cap sources, no
    placeholder data. **The prime directive holds across the whole frontend vocabulary.**
  - **Integrated into the corpus:** all 11 wired into the `Dregg2` root + a Claims §34
    ledger section pinning the Hatchery keystones (Widget left unpinned by design —
    `Basic`'s 2 demo axioms exhibit the amber carrier-bounded tier, which would correctly
    fail a clean-triple pin). **Corpus build CONFIRMED green: `lake build Dregg2.Claims`
    EXIT=0, 3497 jobs, the §34 pins pass** (a wrong name / non-clean pin fails the build).
    Tasks #4 (Hatchery) + #5 (Widgets) complete.
- 2026-06-02 — **Lean RUNS IN A REAL BROWSER (Pillar-4 host pipeline proven).** Closed the
  spike's one open item (it was Node-proxied). Stood up `web/starbridge-host/` (a static
  page loading the spike's REAL `tiny.mjs`/`tiny.wasm`), served it (`python3 -m http.server`,
  `.claude/launch.json` config `starbridge-host`), and loaded it in a real browser via the
  Preview MCP. Verified: `window.__starbridge_status = {ok:true, sum:"42", prod:"42",
  bootMs:12}`, the page paints a golden "42", and the **actual Lean runtime stdout** came
  through (`tiny_add(20,22)=42 / tiny_mul(6,7)=42 / RESULT: PASS`). Provenance on-page:
  0.98 MB wasm, 12 ms warm boot. This is the page→fetch-wasm→boot-Lean→ccall→paint pipeline
  working end-to-end in-browser — the host the verified executor (Rung A), kernel (B), and
  ProofWidgets slot into once the v4.30 wasm runtime build lands. No placeholder: every
  number is a Lean term's output. Honest-failure-wired (the page SAYS so if wasm fails).
- 2026-06-03 — **Pillar 2 Hatchery — Contract.lean's H3 three-apps gate closed + de-duplicated (my
  gate, verified not self-reported).** Reconcile found all 5 `Verify/` modules already green from the
  2026-06-02 fan-out, BUT `Verify/Contract.lean`'s own gate re-expressed only **Identity**
  (`revokedPersists`); the **NameService** + **Subscription** app contracts lived in `Verify/Regression.lean`
  — so `Contract.lean` alone covered 1 of the 3 apps `HATCHERY.md §202` names. Fixed by moving the two app
  contracts (`nameRegisteredContract` / `subWFContract`) into `Contract.lean §3a` as the single source of
  truth (each `step_ob` = the app's OWN proved one-step lemma — `nameservice_step_preserves` /
  `execFullForestA_subWF_preserved`, no fake), with forward reproduction examples against the shipped
  crowns; `Regression.lean` now REUSES them (local dup defs deleted — no name clash, no semantic
  duplication) for its both-directions defeq suite. Now `Contract.lean` self-contains the full H3 gate
  (Identity/NameService/Subscription, all three). **Gate evidence (verify-don't-trust):** `lake build
  Dregg2` EXIT=0, 3497 jobs, zero error / zero sorry; `#print axioms` on `nameRegisteredContract`,
  `subWFContract`, `CellContract.forever/always`, the catalog `gate*` defs, and every reproduced crown
  ⊆ `{propext, Classical.choice, Quot.sound}` (most are just `[propext, Quot.sound]`); non-vacuity has
  TEETH — NameService `isRegistered fma0 alice = false` then `some true` after a real `register`,
  Subscription `subWF` holds on a real committed in-flight-1 ≤ cap-2 queue, the four catalog macros emit
  three distinct `SafetyShape`s. Pillar 2 (H1–H4) complete; H5 `eventually%`/liveness remains deferred to
  the CTL/μ + fairness workflow (honestly omitted, not stubbed).
- **Critical path remaining:** the v4.30 wasm-Lean-runtime build (background) → swap
  `tiny.wasm` → the real executor/kernel/elaborator in the proven host; then Pillars 1B/1C/4
  proper.
