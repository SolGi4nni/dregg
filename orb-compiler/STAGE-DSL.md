# STAGE-DSL — the deep-embedded stage language that ties the deployed serve to the translator

Status: PLAN (grounded in the real tree, 2026-07-14). Nothing below is a proof;
this names the reframe, the one correctness theorem it buys, and the honest
distance to the full 45-stage serve compiling by construction.

Ground facts this plan is checked against (read, not paraphrased):

* Deployed serve — `~/dev/drorb/Reactor/Pipeline.lean`:
  `Stage` is a **record** `{ name, onRequest : Ctx → StageStep,
  onResponse : Ctx → ResponseBuilder → ResponseBuilder }`; `StageStep :=
  respond r | continue c`; the serve is `runPipeline (stages : List Stage)
  appHandler c` folding the onion (request phase in list order, response phase in
  reverse). `~/dev/drorb/Reactor/DeployPipeline.lean` states the running registry
  FLAT: `deployPipelineStages : List Stage`, `deployPipelineStages_length = 45`
  (rfl), and `serveMeteredPipelineConformant` is the host serve
  (`conformantServe` over the dense-arm fold).
* Translator — `~/dev/DreggNet/Pancake/*.lean` (lake package `pancake`, roots in
  `~/dev/DreggNet/lakefile.lean`, Lean 4.30):
  `Pancake.Sem` gives the deep-embedded `PancakeExp` / `PancakeProg` and the
  clocked big-step `PancakeSem : Oracle σ → PancakeProg → PancakeState σ →
  (Option Result × PancakeState σ)`, transcribed clause-for-clause from CakeML
  `ed31510b3`. `Pancake.EmitCorrectCompose` ALREADY carries an embryonic stage
  DSL: `inductive Stage σ = prim | seq | cond`, with `emit : Stage → PancakeProg`,
  `denote : Stage → (PancakeState σ → PancakeState σ)`, and the once-and-for-all
  `emit_correct_generic : WF o st → Refines o (emit st) (denote st)`.

VERIFY-MY-HAND (this session, box-safe `taskset -c 0-15 nice -n 15 lake build`):
the `pancake` package builds GREEN (14 jobs). `#print axioms` on the back-half
keystones is clean — `serialize_write_correct`, `refinesClk_copy`, `copy_step`,
`natToDec_readback` depend on `[propext, Quot.sound]`; `divWhile_sem`,
`divWhile_divmod` on `[propext, Classical.choice, Quot.sound]`. No `sorry`, no
`native_decide`, no `ofReduceBool`. `serveFull_correct` (the current whole-serve
anchor) is read below and is non-vacuous.

---

## 1. DIAGNOSIS — why shallow function-stages block compiling, and what the arc built instead

### 1.1 The deployed stage is a *shallow embedding*

A deployed `Stage` is a pair of **Lean functions**: `onRequest : Ctx →
StageStep` and `onResponse : Ctx → ResponseBuilder → ResponseBuilder`. This is a
*shallow* embedding — the stage's behaviour lives in the host language's function
space. It is perfect for the property the pipeline calculus proves
(`pipeline_stage_effect`, `pipeline_onion_order`, `newStages_collapse`): those
reason about *how any two stages compose*, generically over `onRequest` /
`onResponse`, and close by `rfl`/induction.

But a shallow embedding has no *syntax to recurse on*. A compiler is a function
`Stage → PancakeProg`; you cannot define it by pattern-matching on
`onResponse`, because `onResponse` is an arbitrary `Ctx → ResponseBuilder →
ResponseBuilder` — an opaque element of a function type. There is no `addHeader`
constructor to see, no `if status == 200` node to translate. The deployed 45
stages are, to a compiler, 45 black boxes.

### 1.2 The translator is the compiler *back-half*, keyed off a *deep* embedding

The translator side already commits to the opposite discipline. `PancakeProg` /
`PancakeExp` are **deep** — an inductive syntax `PancakeSem` gives meaning to.
`EmitCorrectCompose.Stage σ` is the embryo of the reframe: it is a deep-embedded
*stage* syntax `{prim, seq, cond}` with **two** interpretations already —

* `emit : Stage → PancakeProg` (the compile leg), and
* `denote : Stage → (PancakeState σ → PancakeState σ)` (the spec leg),

tied by one theorem `emit_correct_generic`. This is exactly the "one syntax, two
interpretations, one correctness theorem" shape. The problem is *which spec* the
`denote` leg targets.

### 1.3 The mismatch that blocks "compile the deployed serve"

`EmitCorrectCompose.denote` produces a **`PancakeState σ → PancakeState σ`**
transformer. The deployed serve is a **`Ctx → StageStep`** /
**`Ctx → ResponseBuilder → ResponseBuilder`** onion. These are different types
over different state. So today there is NO object in the tree of type
"the deployed `Reactor.Pipeline.Stage`" that the translator's `denote` is proven
equal to. The translator compiles *its own* stage denotations; the faithfulness
to the deployed serve is carried, per response, by `#guard serialize resp =
refSerialize resp` (byte-identity to the reference serializer) — a decidable
check on sample responses, **not** a theorem `denote sp = deployedStage`.

### 1.4 The per-stage arc, and its O(N) cost

Because of 1.3, every real serve slice has been assembled by *hand-lifting* each
deployed decision into the translator's `Stage σ` and hand-checking it matches:

* `Pancake/ServeFragment.lean` hand-writes `connLimitDecision`,
  `ipfilterDecision`, `bodyLimitDecision`, `securityHeadersDecision`,
  `methodFilterDecision` — each a `Stage σ` whose `denote` is a bespoke
  `PancakeState` transformer, certified by `emit_correct_generic` (WF discharged
  by `ProofProducing.wf_auto`, zero hand lines) and matched to the deployed
  effect by `#guard` on the routed bytes.
* `Pancake/ServeFull.lean` composes four of them as a decision *prefix* and
  routes the method filter to the structured serialize, yielding
  `serveFull_correct` — a genuine byte-exact memory post-state
  (`MemBytesAt s' base_out (serialize (if signedLt tag 4 then resp200 else
  resp405))`), distinct branches, NOT `P → P`.

`serveFull_correct` is the current high-water mark: **five** real deployed
decisions represented (four executed as a proven prefix, one — the method filter
— driving the response selection) and the response materialised by the
three-segment structured serialize. But it is *one hand-built slice*. Each of the
45 stages would repeat the arc: hand-write its `Stage σ`, hand-argue the deployed
match, hand-thread it into a growing composite. That linear, per-stage, human
cost is the thing the reframe exists to kill.

**The reframe in one sentence:** promote `EmitCorrectCompose.Stage` to a real
`StageProg` whose `denote` leg targets the **deployed `Reactor.Pipeline.Stage`**
(with a proven per-constructor faithfulness theorem, replacing the `#guard`), so
that expressing a stage as a `StageProg` term *automatically* yields both the
deployed stage it denotes and the machine code it compiles to — and the whole
45-stage serve compiles by one fold theorem instead of 45 hand arcs.

---

## 2. DESIGN — `StageProg`: one syntax, two interpretations, one correctness theorem

### 2.1 The syntax

`StageProg` is the deep-embedded serve-stage language. It generalises
`EmitCorrectCompose.Stage σ` from "straight-line state transformer" to "a
deployed pipeline stage" by adding the constructors the 45 deployed shapes need
(§5). The *shape* is:

```
inductive StageProg (σ : Type)
  | pass    (d : Prim σ)                         -- request-phase transform (existing prim)
  | gate    (e : PancakeExp) (g : Ctx → Bool)    -- onRequest may .respond (short-circuit)
            (mk : Ctx → Response)
  | stamp   (e : PancakeExp) (g : Ctx → Bool)    -- onResponse: conditional addHeader
            (hdr : Ctx → String × Bytes)
  | bodyX   (…)                                  -- onResponse: body byte-transform (loop)
  | seq     (s1 s2 : StageProg σ)
  | cond    (e : PancakeExp) (g : Ctx → Bool) (s1 s2 : StageProg σ)
```

(The constructor set is the DSL-growth axis of §5; `pass`/`seq`/`cond` are the
existing `prim`/`seq`/`cond` renamed to the deployed vocabulary.)

### 2.2 Interpretation A — `denote` = the deployed serve (the faithfulness leg)

```
denote : StageProg σ → Reactor.Pipeline.Stage
```

mapping each constructor to a genuine `{ onRequest, onResponse }` record. The
**obligation the reframe pays that the arc only `#guard`ed** is one theorem per
deployed stage:

```
theorem <lib>_denote : denote <lib>Prog = Reactor.Stage.<Lib>.<lib>Stage := by rfl  -- (or by cases-on-Ctx)
```

i.e. the `StageProg` term's denotation is *definitionally the deployed stage
already in `deployPipelineStages`*. This is the "denote must EQUAL the real
Reactor stage, checked" requirement, discharged as a proof, not a sample check.

### 2.3 Interpretation B — `compile` = the translator (the code leg)

```
compile : StageProg σ → PancakeProg     -- = EmitCorrectCompose.emit, extended
```

reusing `emit` for `pass/seq/cond`, and lowering `gate`/`stamp`/`bodyX` through
the back-half (§3). `WF`/`wf_auto` extend to the new constructors.

### 2.4 The one correctness theorem

The translator's existing generic theorem gives, for the *translator* denotation
`tden : StageProg → (PancakeState → PancakeState)`:

```
emit_correct_generic :  WF o sp  →  Refines o (compile sp) (tden sp)
```

The reframe's headline theorem fuses the two legs at the **bytes** — the shape
`serveFull_correct` already proves for the hand slice, lifted to be generic over
any `StageProg` fold:

```
theorem stageprog_serve_correct (sp : StageProg σ) (c : Ctx) (o : Oracle σ) …hWF …hLayout :
    ∃ s',  PancakeSem o (compile sp) (entryOf c) = (none, s') ∧
           MemBytesAt s' base_out (serialize ((runPipeline [denote sp] appHandler c).build))
```

Read: *the compiled Pancake program's output region equals, byte for byte, the
serialized response the deployed pipeline produces for this stage.* Chaining
`<lib>_denote` (§2.2) makes the right-hand side the **actual deployed serve
bytes**. This is the single "correctness theorem" the DSL earns: `denote` = the
running serve, `compile` = the machine code, equal on the wire.

Non-vacuity is inherited from `serveFull_correct`'s witnessed structure: the
conclusion names the real `serialize`, the guard is real routing (`signedLt`),
the branches serialize distinct responses, and `#guard serialize (routedResp 0)
≠ serialize (routedResp 9)` holds.

---

## 3. THE BOTTOM-UP ARC *IS* THE COMPILER BACK-HALF (not wasted)

The reframe does not discard the arc work — it *is* the runtime the `compile`
leg calls. Mapping each arc file to its role under `StageProg`:

| Arc file (built, axiom-clean) | What it proves | Role under `StageProg.compile` |
|---|---|---|
| `Pancake.Sem` | `PancakeExp`/`PancakeProg` + `PancakeSem` (clocked big-step, CakeML-transcribed) | the target language `compile` emits into |
| `Pancake.BytesModel` | `memBytes base len bs s`; `memBytes_load/_store`, `writeByteArray_memBytes` | the DATA layer — response bytes as memory; the semantics of `stamp`/`bodyX` writes |
| `Pancake.SerializeCompile` | `copyWhile` write-loop; `serialize : Response → Bytes`; `serialize_write_correct : MemBytesAt s' base_out (serialize resp)` | lowering a response value to output-region bytes — the `denote`-side response phase, materialised |
| `Pancake.NatToDecCompile` | `divWhile_sem`: `while (10<=n){n:=n-10;q:=q+1}` = divide-by-10 via subtraction (no `Div` in the subset) | how `stamp`/status/Content-Length digits render in-subset — the faithful decimal loop |
| `Pancake.EmitCorrectClock` (`RefinesClk`) | clock-accounting refinement hosting BOTH straight-line and loop stages under one grammar | lets `bodyX`/range loops compose into the same `compile`-correctness fold as `pass` stages |
| `Pancake.EmitCorrectCompose` | `Stage σ`, `emit`/`denote`, `emit_correct_generic` | the DSL embryo `StageProg` extends |
| `Pancake.ProofProducing` (`wf_auto`, `translateCert`) | auto-discharge `WF`; return `(prog, certificate)` | zero-hand-line `WF` for each `StageProg` leaf |
| `Pancake.SerializeFull` / `SerializeHeaders` | structured serialize (`writeSegs`); dynamic header-block writing | the `stamp` constructor's compile target (the header the deployed onion appends) |

The through-line: the arc built a *response is bytes in memory* stack from the
byte algebra up (BytesModel → write-loop → structured/header serialize → decimal
loop), plus the *clock grammar* that lets loops compose. Those are precisely the
lowerings a stage DSL needs for its response phase. The arc was building the
back-half of the compiler the reframe now gives a front-end.

---

## 4. THE PATH — 45 stages → one compile theorem → the dataplane cut

**Phase 0 — retarget `denote` (the reframe proper).** Define `StageProg` and
`denote : StageProg → Reactor.Pipeline.Stage`. Prove `<lib>_denote` for the
handful of stages whose deployed `onRequest`/`onResponse` are already in the
`pass/gate/stamp` shape. Deliverable: the ONE theorem `stageprog_serve_correct`
(§2.4) instantiated on the existing `serveFull` slice, but now with the RHS
routed through `denote sp = <deployed stage>` instead of the hand `resp200/405`.
This is where the `#guard` becomes a `theorem`.

**Phase 1 — grow constructors to cover the deployed shapes (§5).** Add `gate`
(short-circuit), `stamp` (conditional `onResponse` addHeader), `bodyX` (body
loop). Extend `emit`/`compile`, `WF`/`wf_auto`, and `emit_correct_generic`'s
induction to each. Each new constructor is proven ONCE; every stage of that shape
is then free.

**Phase 2 — express `deployPipelineStages` as `[StageProg]`.** Write
`deployPipelineProg : List (StageProg σ)` and prove
`deployPipelineProg.map denote = deployPipelineStages` (the faithfulness of the
whole registry — the list-level lift of §2.2, checked against the real 45-entry
`deployPipelineStages`). This is the gate: it *forces* every `denote` to equal
its deployed stage, so the fold below is about the actual running serve.

**Phase 3 — compile the whole serve by one theorem.** Lift
`stageprog_serve_correct` from `[denote sp]` to the full fold: the compiled
program `compile (foldProg deployPipelineProg)` byte-materialises
`serialize ((runPipeline deployPipelineStages appHandler c).build)`. The onion
order (`pipeline_onion_order`) and the compose rules (`refines_seq`,
`refinesClk` compose) supply the induction; `conformantServe` wraps the result
exactly as `serveMeteredPipelineConformant` does. Deliverable: **one theorem, the
deployed default serve compiled to machine-checkable Pancake, byte-identical to
the running fold.**

**Phase 4 — the Dragon Orb cut (wire into the dataplane).** The emitted `.pnk`
goes `ppFun → cake (CakeML) → object`, linked into the Rust dataplane in place of
the `leanc`-compiled `drorb_serve_pipeline_conformant`. The A1 differential
(machine-code-as-oracle, already the assurance keystone for the region primitive)
runs over the WHOLE composed serve: the emitted binary's output bytes are checked
against `serialize (runPipeline …)` on a request corpus, closing Stack L → machine
code for the deployed serve. This is the datapath goal: verified semantics →
verified codegen → Rust dataplane, `leanc` out of the trusted path.

---

## 5. WHICH STAGES FIT — current constructors vs the DSL growth

Honest coverage against the real 45 in `deployPipelineStages` (categorised by the
deployed `onRequest`/`onResponse` shape; the exact stage names are read from
`DeployPipeline.lean`).

**Fits the CURRENT `{prim/pass, seq, cond}` today (straight-line request-phase
transform, no short-circuit, no `onResponse` header):** the decision stages the
arc already lifted — `securityHeadersDecision`, `connLimitDecision`,
`ipfilterDecision`, `bodyLimitDecision` — plus the method-filter *route* as a
`cond`. **~5 shapes**, and these are the only ones with a `denote = deployed
stage` story reachable without new constructors. Everything below needs growth.

**Needs `gate` (onRequest `.respond` — short-circuit the rest of the onion).**
The deployed gates: `uriTooLongStage` (414), `naGateStage` (406), `methodGate6`,
`welcomeGateStage`, `dashGateStage`, `sseGateStage`, `spaGateStage`,
`sessionGateStage`, `clTeGuardStage`, `jwtAdminStage`, `basicStage`,
`ipfilterStage`, `rateStage`, `redirectStage`, `traversalStage`, `policyStage`,
`mfStage` (Max-Forwards hop), `varyGate8`. **≈18 stages.** `cond` selects between
two *sub-stages* but cannot end the fold; `gate` maps to `StageStep.respond`,
compiling to an early `Return` of the gate response.

**Needs `stamp` (onResponse conditional `addHeader`).** The plus2 response-stamp
edges — `altStage`, `ppStage`, `corpStage`, `viaStage`, `csStage`,
`warningStage`, `linkStage`, `proxyProtoStage`, `swrStage` — plus `taoStage`,
`contentLocationStage`, `langStampStage`, `dashTypeStage`, `spaTypeStage`,
`sseHeadStage`, `cookieSecureStage`, `setCookieStage`, `cacheControlStage`
(status-gated), `deployCorsStage`, `headerRewriteStage`, `securityheadersStage`,
`headerStage`. **≈22 stages.** Compiles through `SerializeHeaders`' dynamic
header-block write (the outer header loop named as a residual in
`SerializeFull.lean`); the status-gated ones (`cacheControlStage` on `200` static
GET) add a `cond` on the builder status.

**Needs `bodyX` (onResponse body byte-transform).** `gzipStage`,
`htmlrewriteStage`. **2 stages.** Compiles through a `RefinesClk` body loop
(`EmitCorrectClock` already hosts loop stages).

**Needs a loop/range constructor.** `rangeUnveilStage`, `multiRangeStage`
(206 slicing / If-Range). **2 stages.** These are the deepest — a loop over
range specs, body slicing — and lean hardest on `RefinesClk` + `BytesModel`.

**Honest stage-coverage count.** Deployed stages with a *proven* `denote =
deployed Reactor stage` faithfulness today: **0** (the arc proves the translator
against its own hand-written `denote` and `#guard`s the bytes; it never states
`denote = <a stage in deployPipelineStages>`). Deployed stages whose SHAPE fits
the current constructors, so Phase-0/-2 can prove faithfulness without DSL
growth: **~5** (the four decision stages + the method route). Remaining **40**
need the four new constructors — `gate` (≈18), `stamp` (≈22), `bodyX` (2), range
loop (2); several stages combine shapes (e.g. `varyGate8` = stamp + gate), so the
constructor is the unit of proof, not the stage: **4 new constructors** unlock
the full 45.

---

## RESIDUALS (named, not hidden)

1. **`denote = deployed stage` is unproven for all 45.** The whole plan rests on
   Phase 0/2 discharging `<lib>_denote` and `deployPipelineProg.map denote =
   deployPipelineStages`. Until then the translator's faithfulness to the running
   serve is `#guard`-level (sample byte-identity to `refSerialize`), not a
   theorem. This is the single largest honesty gap and the first thing to build.
2. **The four new constructors are shapes, not yet Lean.** `gate`/`stamp`/`bodyX`/
   range are specified here; each needs its `compile`, its `denote` record, its
   `WF`/`wf_auto` clause, and its induction case in the generic theorem. Only
   `pass/seq/cond` exist today.
3. **`serveFull_correct` is Stack L (the Lean model of Pancake), not machine
   code.** The A1 machine-code differential exists for the region primitive but
   NOT yet for the composed serve; Phase 4 owes it over the whole `.pnk`.
4. **Output region is word-addressed in the current write-loop.** Packed byte
   layout needs `StoreByte` throughout (now modelled in `Sem`/`Lower`, used by
   `NatToDecCompile`/`digit_store`, but the structured serialize's segment copy is
   still word-addressed). Shared bytes-lowering residual.
5. **Admission results do not yet short-circuit.** In `serveFull_correct` the four
   decision stages are *executed* but only the method filter drives the response;
   an admission failure should route to 503/403/413. That is exactly what the
   `gate` constructor (§5) is for — the residual is the same one the arc named.
6. **`conformantServe` owns the date conditionals (J09/J11).** Per
   `DeployPipeline.lean`'s own note, the RFC wrapper strips `If-None-Match`/
   `If-Match` before the inner fold, so those stages live in the wrapper, not the
   45-list. Any `StageProg` fold theorem inherits this wrapper boundary.

## Build / verify provenance

* `cd ~/dev/DreggNet && PATH=$HOME/.elan/bin:$PATH taskset -c 0-15 nice -n 15
  lake build` → **Build completed successfully (14 jobs)**, Lean 4.30.
* Back-half `#print axioms`: `serialize_write_correct`, `refinesClk_copy`,
  `copy_step`, `natToDec_readback` → `[propext, Quot.sound]`; `divWhile_sem`,
  `divWhile_divmod`, `divWhile_matches_decAux_step` → `[propext,
  Classical.choice, Quot.sound]`. No `sorry` / `native_decide` / `ofReduceBool`.
* `serveFull_correct` statement read in full: conclusion is
  `MemBytesAt s' base_out (serialize (if signedLt tag 4 then resp200 else
  resp405))` with distinct branch responses — non-vacuous.
