import Reactor.Pipeline
import Dsl.Component

/-!
# Dsl.Cfg.Middleware — the middleware dimension of a deployment

A deployment threads a request through an **ordered middleware chain**: a
`List Stage`, run request-phase in list order and response-phase in reverse (the
onion, `Reactor.Pipeline.runPipeline`). This file owns ONLY that dimension.

The dimension has two layers:

* the **load-bearing** `MiddlewareCfg.chain : List Stage` — exactly the stage list
  `Reactor.Pipeline.runPipeline` folds over, the value `Dsl.instantiate` hands to the
  deployed serve; and
* the **declarative surface** `MiddlewarePlan` — the full pkl-style middleware
  authoring surface (a named `StageLib` registry, an arbitrary ordered chain of
  entries referencing library stages by name, per-entry CONDITIONAL composition, and
  PER-ROUTE overrides) that `compile`s down to that `List Stage`. `MiddlewareCfg.ofPlan`
  is the smart constructor: it populates `chain` with `plan.compile`, so `instantiate`
  honors the declarative surface with NO change to its `cfg.middleware.chain` read.

## Correct-by-construction

Every declarative combinator compiles into a plain `Stage` (`Stage.guard` wraps a
library stage behind a predicate; a per-route override is that guard over a route
match), so the compiled chain is an ordinary `List Stage` and the WHOLE proven
pipeline calculus (`pipeline_cons`, `pipeline_gate_short_circuits`,
`pipeline_gate_status`, `pipeline_stage_effect`, `pipeline_onion_order`) applies to
it UNCHANGED — no re-proof per config. The status-stability of the compiled chain is
recovered through the package **component calculus**: the chain is a reachable state
of a `chainBuilder : Dsl.Component`, so `Component.reachable_inv` (invariant
preservation composes) delivers `chainInv` (every stage status-stable) for free, and
`Component.prod_preserves` (components compose) shows a global chain and a per-route
override chain preserve their conjoined invariant in parallel.

## What this expresses that the flat serve could not

The deployed `deployStagesFull2` is a FLAT literal that applies every transform to
every admitted response and hand-wraps each scoped gate as a bespoke `*Stage` def
(e.g. `jwtAdminStage` = "jwt, but only on `/admin`"). The declarative surface lifts
that scoping into CONFIGURATION over the unchanged library: `.guarded onStatic "gzip"`
gzips only `/static`, `.guarded onApi "cors"` CORS-stamps only `/api`, `.routed`
attaches a whole sub-chain to one route — none of which the flat list can say without
new code (see `demoPlan` and its per-path effect theorems below).
-/

namespace Dsl.Cfg

open Reactor.Pipeline
open Reactor (Response)
open Proto (Request Bytes)

/-! ## The load-bearing dimension -/

/-- The middleware dimension: the ordered stage chain. Request phase runs in list
order; response phase runs in reverse (the onion). This is precisely the
`List Stage` `Reactor.Pipeline.runPipeline` folds over, and the value
`Dsl.instantiate` reads as `cfg.middleware.chain`. -/
structure MiddlewareCfg where
  /-- The ordered middleware chain. -/
  chain : List Stage

/-- Append a stage to the end of the chain — the one-line grow operation a new
middleware lane performs (mirrors appending to the registered stage list). -/
def MiddlewareCfg.append (m : MiddlewareCfg) (s : Stage) : MiddlewareCfg :=
  { m with chain := m.chain ++ [s] }

/-- Prepend a stage to the front of the chain (an outermost gate). -/
def MiddlewareCfg.prepend (s : Stage) (m : MiddlewareCfg) : MiddlewareCfg :=
  { m with chain := s :: m.chain }

/-! ## Conditional composition — the one combinator everything compiles through

`Stage.guard p s` is the primitive of the declarative surface: it runs stage `s`
EXACTLY when the predicate `p` holds on the context, and is a pure pass-through
otherwise (request continues unchanged, response untouched). A conditional entry is
one guard; a per-route override is a guard whose predicate is a route match. The
guarded value is STILL a `Stage`, so the pipeline calculus reasons about it with no
new lemmas — only the two `guard_*_pos` / `guard_*_neg` reductions below. -/

/-- **Conditional stage.** `Stage.guard p s` behaves as `s` on contexts where `p c`
holds, and as the identity pass-through elsewhere. The unit of conditional and
per-route middleware composition. -/
def Stage.guard (p : Ctx → Bool) (s : Stage) : Stage where
  name := s.name
  onRequest := fun c => if p c then s.onRequest c else .continue c
  onResponse := fun c b => if p c then s.onResponse c b else b

/-- When the predicate holds, the guard's request phase IS the underlying stage's. -/
theorem guard_onRequest_pos {p : Ctx → Bool} {s : Stage} {c : Ctx} (h : p c = true) :
    (Stage.guard p s).onRequest c = s.onRequest c := by
  simp [Stage.guard, h]

/-- When the predicate fails, the guard's request phase passes through unchanged. -/
theorem guard_onRequest_neg {p : Ctx → Bool} {s : Stage} {c : Ctx} (h : p c = false) :
    (Stage.guard p s).onRequest c = .continue c := by
  simp [Stage.guard, h]

/-- When the predicate holds, the guard's response phase IS the underlying stage's. -/
theorem guard_onResponse_pos {p : Ctx → Bool} {s : Stage} {c : Ctx} {b : ResponseBuilder}
    (h : p c = true) :
    (Stage.guard p s).onResponse c b = s.onResponse c b := by
  simp [Stage.guard, h]

/-- When the predicate fails, the guard's response phase leaves the builder untouched. -/
theorem guard_onResponse_neg {p : Ctx → Bool} {s : Stage} {c : Ctx} {b : ResponseBuilder}
    (h : p c = false) :
    (Stage.guard p s).onResponse c b = b := by
  simp [Stage.guard, h]

/-- **Guarding preserves status-stability.** If `s`'s response phase never changes
the status, neither does `Stage.guard p s` (it is either `s`'s phase or the
identity). So a conditional/per-route stage still keeps a gate short-circuit's status
through the onion (`Pipeline.pipeline_gate_status`). -/
theorem guard_statusStable {p : Ctx → Bool} {s : Stage} (h : Stage.statusStable s) :
    Stage.statusStable (Stage.guard p s) := by
  intro c b
  cases hpc : p c with
  | true  => rw [guard_onResponse_pos hpc]; exact h c b
  | false => rw [guard_onResponse_neg hpc]

/-! ## The stage library (registry) — reference stages by name

The declarative surface references library stages by NAME. A `StageLib` is the
registry a deployment welds its `Reactor.Stage.*` library into; a config names the
stages it wants and `resolve` looks them up (falling back to the identity
`passStage`, so `compile` is total). -/

/-- The identity pass-through stage: request continues unchanged, response untouched.
The fallback a name-lookup returns for an unregistered name, and the neutral element
of chain composition. -/
def passStage : Stage where
  name := "pass"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b

/-- `passStage`'s response phase is the identity — trivially status-stable. -/
theorem passStage_statusStable : Stage.statusStable passStage := fun _ _ => rfl

/-- The named stage registry — the library a config draws its chain from. -/
structure StageLib where
  /-- The registered `(name, stage)` bindings. -/
  stages : List (String × Stage)

/-- Look a stage up by name (the first binding wins). -/
def StageLib.find? (lib : StageLib) (name : String) : Option Stage :=
  (lib.stages.find? (fun kv => kv.1 == name)).map (·.2)

/-- Resolve a name to its library stage, or the identity `passStage` if unbound —
total, so `compile` never fails on an unknown name. -/
def StageLib.resolve (lib : StageLib) (name : String) : Stage :=
  (lib.find? name).getD passStage

/-- A library is status-stable when every registered stage is. -/
def StageLib.statusStable (lib : StageLib) : Prop :=
  ∀ nv ∈ lib.stages, Stage.statusStable nv.2

/-- Resolving any name against a status-stable library yields a status-stable stage
(a hit is a registered stage; a miss is `passStage`). -/
theorem StageLib.resolve_statusStable {lib : StageLib} (h : lib.statusStable)
    (name : String) : Stage.statusStable (lib.resolve name) := by
  unfold StageLib.resolve StageLib.find?
  cases hf : lib.stages.find? (fun kv => kv.1 == name) with
  | none => simpa using passStage_statusStable
  | some nv => simpa using h nv (List.mem_of_find?_eq_some hf)

/-! ## The declarative entries and the plan -/

/-- One entry of a declarative middleware chain. -/
inductive MwEntry where
  /-- Reference a library stage by name, applied unconditionally. -/
  | named (name : String)
  /-- Conditional composition: apply the named stage ONLY where `p` holds. -/
  | guarded (p : Ctx → Bool) (name : String)
  /-- Per-route override: apply the named sub-chain ONLY to requests matching `rk`. -/
  | routed (rk : Request → Bool) (names : List String)

/-- Compile one entry to the `List Stage` it contributes. A `named` entry resolves to
one stage; a `guarded` entry to one `Stage.guard`; a `routed` entry to the whole
sub-chain, each stage guarded by the route match. Every combinator lands in a plain
`Stage`, so the compiled list is an ordinary pipeline. -/
def MwEntry.compile (lib : StageLib) : MwEntry → List Stage
  | .named name    => [lib.resolve name]
  | .guarded p name => [Stage.guard p (lib.resolve name)]
  | .routed rk names => (names.map lib.resolve).map (Stage.guard (fun c => rk c.req))

/-- Shape of a `routed` entry's compilation (documentation lemma). -/
theorem routed_compile (rk : Request → Bool) (names : List String) (lib : StageLib) :
    (MwEntry.routed rk names).compile lib
      = (names.map lib.resolve).map (Stage.guard (fun c => rk c.req)) := rfl

/-- **The declarative middleware plan.** A registry plus an ORDERED list of entries —
the full pkl authoring surface: arbitrary ordered composition, per-entry conditional
application, and per-route sub-chains, all over a named library. -/
structure MiddlewarePlan where
  /-- The stage library the entries name into. -/
  lib : StageLib
  /-- The ordered entries. -/
  entries : List MwEntry

/-- **Compile a plan to the deployed `List Stage`.** Concatenate each entry's
contribution in order — exactly the fold `Reactor.Pipeline.runPipeline` consumes. -/
def MiddlewarePlan.compile (pl : MiddlewarePlan) : List Stage :=
  (pl.entries.map (MwEntry.compile pl.lib)).flatten

/-- **The smart constructor.** Build a `MiddlewareCfg` from a declarative plan by
compiling it into the load-bearing `chain`. `Dsl.instantiate` reads `chain`
unchanged, so a config authored as a `MiddlewarePlan` flows straight to the deployed
serve. -/
def MiddlewareCfg.ofPlan (pl : MiddlewarePlan) : MiddlewareCfg :=
  { chain := pl.compile }

/-- The compiled plan IS the chain `instantiate` folds — the declarative surface and
the load-bearing list agree by construction. -/
@[simp] theorem MiddlewareCfg.ofPlan_chain (pl : MiddlewarePlan) :
    (MiddlewareCfg.ofPlan pl).chain = pl.compile := rfl

/-! ## Composition correctness

Two facts make the compiled chain correct-by-construction:

1. it is a plain `List Stage`, so the entire proven pipeline calculus applies with no
   re-proof (`guard_*` are the only new reductions); and
2. status-stability of every compiled stage — recovered THROUGH the package component
   calculus (`Component.reachable_inv`), then combined with `pipeline_gate_status` to
   get the deployed "a config's short-circuit keeps its status" guarantee. -/

/-- The invariant on a compiled stage list: every stage is status-stable. -/
def chainInv (chain : List Stage) : Prop := ∀ s ∈ chain, Stage.statusStable s

/-- Each compiled entry contributes only status-stable stages (guarding preserves it). -/
theorem MwEntry.compile_statusStable {lib : StageLib} (hlib : lib.statusStable)
    (e : MwEntry) : ∀ s ∈ e.compile lib, Stage.statusStable s := by
  cases e with
  | named name =>
    intro s hs
    simp only [MwEntry.compile, List.mem_singleton] at hs
    subst hs
    exact lib.resolve_statusStable hlib name
  | guarded p name =>
    intro s hs
    simp only [MwEntry.compile, List.mem_singleton] at hs
    subst hs
    exact guard_statusStable (lib.resolve_statusStable hlib name)
  | routed rk names =>
    intro s hs
    simp only [MwEntry.compile, List.mem_map] at hs
    obtain ⟨a, ⟨name, _hn, rfl⟩, rfl⟩ := hs
    exact guard_statusStable (lib.resolve_statusStable hlib name)

/-- The whole compiled plan is status-stable when the library is. -/
theorem MiddlewarePlan.compile_statusStable {pl : MiddlewarePlan}
    (hlib : pl.lib.statusStable) : chainInv pl.compile := by
  intro s hs
  simp only [MiddlewarePlan.compile, List.mem_flatten, List.mem_map] at hs
  obtain ⟨l, ⟨e, _he, rfl⟩, hsl⟩ := hs
  exact MwEntry.compile_statusStable hlib e s hsl

/-! ### The component-calculus route to `chainInv`

The status-stability of a compiled chain is delivered by the package
`Dsl.Component` kernel, not a bespoke induction: a chain grown one status-stable
stage at a time is a REACHABLE state of the `chainBuilder` component, and
`Component.reachable_inv` (invariant preservation composes) recovers `chainInv` on
every reachable state. -/

/-- A status-stable stage — the input alphabet of `chainBuilder`. -/
def SStage : Type := { s : Stage // Stage.statusStable s }

/-- **The chain-builder component.** State is the accumulated `List Stage`; each step
appends a status-stable stage; the invariant is `chainInv`. A direct instance of the
package component calculus. -/
def chainBuilder : Dsl.Component where
  State := List Stage
  Input := SStage
  Output := Unit
  inv := chainInv
  init := []
  step := fun chain s => (chain ++ [s.val], [])
  init_wf := by intro s hs; simp at hs
  step_wf := by
    intro chain s h t ht
    rcases List.mem_append.mp ht with h1 | h1
    · exact h t h1
    · rw [List.mem_singleton.mp h1]; exact s.property

/-- Replaying stages one at a time from an accumulator rebuilds the concatenation. -/
theorem chainBuilder_runState (acc : List Stage) (ss : List SStage) :
    chainBuilder.runState acc ss = acc ++ ss.map Subtype.val := by
  induction ss generalizing acc with
  | nil => simp [Dsl.Component.runState, Dsl.Component.run]
  | cons a rest ih =>
    have hstep : chainBuilder.runState acc (a :: rest)
        = chainBuilder.runState (acc ++ [a.val]) rest := rfl
    rw [hstep, ih]
    simp [List.map_cons]

/-- Any status-stable stage list has a witness `List SStage` that maps back to it. -/
theorem exists_wrap {chain : List Stage} (h : chainInv chain) :
    ∃ ss : List SStage, ss.map Subtype.val = chain := by
  induction chain with
  | nil => exact ⟨[], rfl⟩
  | cons a rest ih =>
    have ha : Stage.statusStable a := h a (List.mem_cons_self a rest)
    have hrest : chainInv rest := fun s hs => h s (List.mem_cons_of_mem a hs)
    obtain ⟨ss, hss⟩ := ih hrest
    exact ⟨(⟨a, ha⟩ : SStage) :: ss, by simp [hss]⟩

/-- **Every status-stable chain is `chainBuilder`-reachable.** Replay it stage by
stage from the empty chain. -/
theorem chainBuilder_reachable {chain : List Stage} (h : chainInv chain) :
    chainBuilder.Reachable chain := by
  obtain ⟨ss, hss⟩ := exists_wrap h
  exact ⟨ss, by rw [chainBuilder_runState]; simp [chainBuilder, hss]⟩

/-- **The component-calculus payoff.** A compiled plan (over a status-stable library)
is status-stable — obtained by running the plan's chain through the package's
`Component.reachable_inv` (invariant preservation composes), applied to the middleware
dimension. -/
theorem compiled_chain_statusStable {pl : MiddlewarePlan} (hlib : pl.lib.statusStable) :
    chainInv pl.compile :=
  Dsl.Component.reachable_inv chainBuilder
    (chainBuilder_reachable (MiddlewarePlan.compile_statusStable hlib))

/-- **Components compose.** Two middleware chain-builders — e.g. the global chain and
a per-route override chain — run in parallel; their product preserves the conjoined
`chainInv ∧ chainInv` invariant. Direct instance of `Component.prod_preserves`. -/
theorem chainBuilder_prod_preserves
    (s : (chainBuilder.prod chainBuilder).State)
    (i : (chainBuilder.prod chainBuilder).Input)
    (h : (chainBuilder.prod chainBuilder).inv s) :
    (chainBuilder.prod chainBuilder).inv ((chainBuilder.prod chainBuilder).step s i).1 :=
  Dsl.prod_preserves chainBuilder chainBuilder s i h

/-- **The deployed consequence.** If a compiled chain's first stage gates
`.respond r` and the library is status-stable, the built pipeline response keeps
status `r.status`: the config's short-circuit (a 401/403/…) survives the whole inner
response onion. Combines the component-calculus invariant
(`compiled_chain_statusStable`) with the pipeline calculus (`pipeline_gate_status`). -/
theorem compiled_gate_status {pl : MiddlewarePlan} (hlib : pl.lib.statusStable)
    (s : Stage) (rest : List Stage) (handler : Ctx → Response) (c : Ctx) (r : Response)
    (hchain : pl.compile = s :: rest)
    (hg : s.onRequest c = .respond r) :
    ((runPipeline pl.compile handler c).build).status = r.status := by
  have hss : chainInv pl.compile := compiled_chain_statusStable hlib
  rw [hchain] at hss ⊢
  exact Reactor.Pipeline.pipeline_gate_status s rest handler c r hg
    (fun t ht => hss t (List.mem_cons_of_mem s ht))

/-! ## Demonstration — a config the flat hardcoded serve could not express

The deployed `deployStagesFull2` gzips and CORS-stamps EVERY admitted response
identically. Expressing "gzip only `/static`, CORS only `/api`" there needs two new
bespoke `*Stage` defs. Here it is pure configuration over an unchanged library. -/

/-- `Content-Encoding: gzip` as a wire header pair. -/
def gzipEncHeader : Bytes × Bytes :=
  ("content-encoding".toUTF8.toList, "gzip".toUTF8.toList)

/-- A schematic gzip transform: always passes, stamps `Content-Encoding: gzip` on the
response. Status-stable (a header push never touches the status). -/
def demoGzipStage : Stage where
  name := "gzip"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.addHeader gzipEncHeader

theorem demoGzipStage_statusStable : Stage.statusStable demoGzipStage := fun _ _ => rfl

/-- `Access-Control-Allow-Origin: *` as a wire header pair. -/
def acaoHeader : Bytes × Bytes :=
  ("access-control-allow-origin".toUTF8.toList, "*".toUTF8.toList)

/-- A schematic CORS transform: always passes, stamps `Access-Control-Allow-Origin`. -/
def demoCorsStage : Stage where
  name := "cors"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.addHeader acaoHeader

theorem demoCorsStage_statusStable : Stage.statusStable demoCorsStage := fun _ _ => rfl

/-- The demo library: `gzip` and `cors` registered by name. -/
def demoLib : StageLib :=
  { stages := [("gzip", demoGzipStage), ("cors", demoCorsStage)] }

theorem demoLib_statusStable : demoLib.statusStable := by
  intro nv hnv
  simp only [demoLib, List.mem_cons, List.not_mem_nil, or_false] at hnv
  rcases hnv with rfl | rfl <;> exact fun _ _ => rfl

/-- Structural byte-prefix test (structural on the needle). -/
def bytesPrefix : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && bytesPrefix as bs

/-- Does the request target begin with `pfx`? -/
def targetHasPrefix (pfx : Bytes) (req : Request) : Bool := bytesPrefix pfx req.target

/-- `/static` as ASCII bytes. -/
def staticPrefix : Bytes := "/static".toUTF8.toList
/-- `/api` as ASCII bytes. -/
def apiPrefix : Bytes := "/api".toUTF8.toList

/-- The context is a `/static/*` request. -/
def onStatic (c : Ctx) : Bool := targetHasPrefix staticPrefix c.req
/-- The context is an `/api/*` request. -/
def onApi (c : Ctx) : Bool := targetHasPrefix apiPrefix c.req

/-- **A config the flat hardcoded serve could not express.** `gzip` applies ONLY to
`/static/*` responses and `cors` ONLY to `/api/*` responses — per-path conditional
middleware, authored as configuration over the unchanged `demoLib`. The flat
`deployStagesFull2` cannot say this without two new bespoke stage defs. -/
def demoPlan : MiddlewarePlan :=
  { lib := demoLib
    entries := [ .guarded onStatic "gzip"
               , .guarded onApi "cors" ] }

/-- The demo plan compiles to the two guarded stages, in order. -/
theorem demoPlan_compile :
    demoPlan.compile
      = [Stage.guard onStatic (demoLib.resolve "gzip"),
         Stage.guard onApi (demoLib.resolve "cors")] := by
  rfl

/-- The demo plan is status-stable (its library is), via the component calculus. -/
theorem demoPlan_statusStable : chainInv demoPlan.compile :=
  compiled_chain_statusStable demoLib_statusStable

/-- **The conditional FIRES on `/static`.** On a `/static` request the gzip guard's
response phase stamps `Content-Encoding: gzip`. -/
theorem gzip_fires_on_static {c : Ctx} {b : ResponseBuilder} (h : onStatic c = true) :
    (Stage.guard onStatic demoGzipStage).onResponse c b = b.addHeader gzipEncHeader := by
  rw [guard_onResponse_pos h]; rfl

/-- **The SAME conditional BYPASSES off `/static`.** On any non-`/static` request the
gzip guard leaves the response untouched — no `Content-Encoding`. This per-path
differentiation is exactly what a flat stage list cannot express without new code. -/
theorem gzip_bypasses_off_static {c : Ctx} {b : ResponseBuilder} (h : onStatic c = false) :
    (Stage.guard onStatic demoGzipStage).onResponse c b = b := by
  rw [guard_onResponse_neg h]

/-- **Wire-level effect: the header reaches the built response, only on `/static`.**
On a `/static` request, the compiled demo chain's built output carries
`Content-Encoding: gzip` — proved through the real pipeline fold
(`pipeline_stage_effect`), for any handler. The gzip guard passes its request phase
(a transform), so the effect rides the response onion into the finalized `Response`. -/
theorem demo_gzip_present_on_static (handler : Ctx → Response) (c : Ctx)
    (hs : onStatic c = true) :
    gzipEncHeader ∈
      ((runPipeline [Stage.guard onStatic demoGzipStage, Stage.guard onApi demoCorsStage]
          handler c).build).headers := by
  have h1 : (Stage.guard onStatic demoGzipStage).onRequest c = .continue c := by
    rw [guard_onRequest_pos hs]; rfl
  rw [Reactor.Pipeline.pipeline_stage_effect _ _ handler c c h1,
      guard_onResponse_pos hs]
  show gzipEncHeader ∈
    (((runPipeline [Stage.guard onApi demoCorsStage] handler c).addHeader gzipEncHeader).build).headers
  rw [Reactor.Pipeline.build_addHeader]
  simp

end Dsl.Cfg
