import Reactor.Pipeline
import Reactor.Stage.SpaFallback
import StaticFile

/-!
# Reactor.Stage.SpaServe — the deployed SPA fallback route (PARITY-LEDGER rt.7)

rt.7 was PARTIAL-inert: `Reactor.Stage.SpaFallback` proved the SPA serving
discipline (`spa_fallback_serves_index`, `spa_fallback_no_escape`,
`spa_real_file_served`) over an uninterpreted filesystem boundary, but the proven
leaf was wired into no binary — a navigable client route was still a deployed
`404`. This module supplies the missing half:

* `spaGateStage` — a request-phase gate: `GET` under the `/app/` prefix is
  answered `200` whose body is the deployed content of the path the PROVEN
  `spaServedPath` selects — the model's response selection, instantiated at the
  REAL embedded filesystem (`StaticFile.staticFS`) and driving the deployed bytes.
* `spaTypeStage` — a response-phase stamp on the same scope:
  `Content-Type: text/html` (the SPA shell's media type), placed OUTSIDE the
  deployed rewrite onion so the shell markup reaches the wire intact.

The gate is PREFIX-SCOPED (only `GET /app/…`), so every non-SPA route — including
the conformance suites' `404` probes — keeps its exact deployed behaviour.

## What is proved here (all pure kernel)

* `resolved_under_app` / `spa_resolved_not_file` — every `/app/…` request resolves
  under the `app` document root (the escape-safe traversal), where the REAL
  embedded FS has no regular file; hence
* `spa_always_index` — the deployed instantiation always selects the SPA index
  (the model's `spa_fallback_serves_index`, its filesystem hypothesis DISCHARGED
  against the real FS rather than assumed), and
* `spaRespOf_body` — the deployed gate body IS the shell at the model-selected
  index path.
* `deployed_no_escape` — the served path never escapes the `app` root, even under
  a `..`-popping filesystem walker (the model's no-escape, instantiated).
* `spaGate_fires` / `spaGate_passes`, `spaTypeStage_effect` / `_noop` — exact
  scoping of the gate and the stamp.
-/

namespace Reactor.Stage.SpaServe

open Reactor.Pipeline
open Proto (Bytes)
open Reactor.Stage.SpaFallback

/-- ASCII `"GET"`. -/
def getBytes : Bytes := [71, 69, 84]

/-- ASCII `"/app/"` — the SPA route prefix (scoped: nothing outside it changes). -/
def spaPrefix : Bytes := [47, 97, 112, 112, 47]

/-- ASCII `"Content-Type"`. -/
def ctName : Bytes := [67, 111, 110, 116, 101, 110, 116, 45, 84, 121, 112, 101]

/-- ASCII `"text/html"`. -/
def htmlVal : Bytes := [116, 101, 120, 116, 47, 104, 116, 109, 108]

/-- ASCII `"OK"`. -/
def okReason : Bytes := [79, 75]

/-- The route's guard: method `GET`, target under `/app/`. -/
def inScope (c : Ctx) : Bool :=
  c.req.method == getBytes && spaPrefix.isPrefixOf c.req.target

/-- The SPA shell (the application index the fallback serves): real markup with
the client bootstrap pointing at the deployed static asset. -/
def shellBytes : Bytes :=
  "<!doctype html><html><head><title>app</title></head><body><div id=\"root\"></div><script src=\"/static/app.js\"></script></body></html>".toUTF8.toList

/-- **The deployed SPA configuration**: document root `app`, the REAL embedded
filesystem (`StaticFile.staticFS` — the exact boundary the deployed static route
serves from), index `index.html`. This is the model's `Config` with its
uninterpreted `isFile` boundary INTERPRETED at the deployed FS. -/
def deployedSpaCfg : Config where
  docRoot := ["app"]
  isFile := fun p => (StaticFile.staticFS p).isSome
  indexRel := ["index.html"]

/-- Deployed content of a resolved path: the real embedded bytes when the FS holds
a regular file there, the SPA shell otherwise. -/
def contentOf (p : List String) : Bytes := (StaticFile.staticFS p).getD shellBytes

/-- Split bytes on `/` (structural, kernel-reducible). -/
def splitSlash : Bytes → List Bytes
  | [] => [[]]
  | b :: t =>
    if b == (47 : UInt8) then [] :: splitSlash t
    else match splitSlash t with
      | [] => [[b]]
      | s :: rest => (b :: s) :: rest

/-- Split a target's byte path into segments the model resolves (`/`-separated,
leading slash dropped). -/
def segsOf (target : Bytes) : List String :=
  (splitSlash (target.drop 1)).map
    (fun seg => String.mk (seg.map (fun b => Char.ofNat b.toNat)))

/-- The gate's response: `200` serving the deployed content of the path the PROVEN
`spaServedPath` selects for this request — the model drives the bytes. -/
def spaRespOf (c : Ctx) : Reactor.Response :=
  { status := 200, reason := okReason, headers := []
    body := contentOf (spaServedPath deployedSpaCfg (segsOf c.req.target)) }

/-- **The SPA fallback gate.** Answers any `GET /app/…` target with the
model-selected content; passes everything else through untouched (prefix-scoped). -/
def spaGateStage : Stage where
  name := "spa-fallback"
  onRequest := fun c => if inScope c then .respond (spaRespOf c) else .continue c
  onResponse := fun _ b => b

/-- **The SPA media-type stamp.** Response phase: on `GET /app/…`, push
`Content-Type: text/html`; identity elsewhere. Placed OUTSIDE the deployed
rewrite onion (whose body transform is content-type-gated on the INNER response),
so the shell markup reaches the wire intact. -/
def spaTypeStage : Stage where
  name := "spa-head"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if inScope c then b.addHeader (ctName, htmlVal) else b

/-! ## The guard -/

theorem inScope_true (c : Ctx) (hm : c.req.method = getBytes)
    (ht : spaPrefix.isPrefixOf c.req.target = true) : inScope c = true := by
  unfold inScope
  rw [hm, ht]
  rfl

theorem inScope_false_of_prefix (c : Ctx)
    (h : spaPrefix.isPrefixOf c.req.target = false) : inScope c = false := by
  unfold inScope
  rw [h, Bool.and_false]

/-! ## The deployed filesystem facts -/

/-- The REAL embedded FS holds no regular file under the `app` root: the only
asset lives under `static`. -/
theorem staticFS_app_none (t : List String) :
    StaticFile.staticFS ("app" :: t) = none := rfl

/-- Every raw request resolves UNDER the `app` document root (the escape-safe
traversal clamps it there): the resolved path is `"app" ::` the normalized tail. -/
theorem resolved_under_app (raw : List String) :
    resolveTarget deployedSpaCfg raw = "app" :: Route.Path.normalize raw := by
  show Safety.Traversal.serveStatic ["app"] raw = _
  rw [Safety.Traversal.serveStatic_eq_normalize]
  rfl

/-- **The deployed FS hypothesis, DISCHARGED**: no `/app/…` request resolves to a
regular file of the real embedded FS. (This is the `hmiss` the model's fallback
theorem assumes; here it is a fact of the deployed filesystem, not an assumption.) -/
theorem spa_resolved_not_file (raw : List String) :
    deployedSpaCfg.isFile (resolveTarget deployedSpaCfg raw) = false := by
  rw [resolved_under_app]
  show (StaticFile.staticFS ("app" :: Route.Path.normalize raw)).isSome = false
  rw [staticFS_app_none]
  rfl

/-- **The deployed fallback always selects the SPA index** — the model's
`spa_fallback_serves_index`, instantiated at the real FS (and the plain serve
would have `404`ed, same instantiation). -/
theorem spa_always_index (raw : List String) :
    spaServe deployedSpaCfg raw = .ok deployedSpaCfg.indexPath
  ∧ (spaServe deployedSpaCfg raw).status = 200
  ∧ plainServe deployedSpaCfg raw = .notFound := by
  have h := spa_fallback_serves_index deployedSpaCfg raw (spa_resolved_not_file raw)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The served path selection: always the index path (`spaServedPath` under the
discharged FS fact). -/
theorem spaServedPath_index (raw : List String) :
    spaServedPath deployedSpaCfg raw = deployedSpaCfg.indexPath := by
  unfold spaServedPath
  rw [if_neg]
  rw [spa_resolved_not_file raw]
  simp

/-- The deployed content at the index path is the shell (the FS holds no file
there — `app/index.html` is the embedded shell, not a `static` asset). -/
theorem contentOf_indexPath : contentOf deployedSpaCfg.indexPath = shellBytes := by
  show (StaticFile.staticFS ("app" :: ["index.html"])).getD shellBytes = _
  rw [staticFS_app_none]
  rfl

/-- **The deployed gate body IS the shell** at the model-selected index path — for
EVERY request context. -/
theorem spaRespOf_body (c : Ctx) : (spaRespOf c).body = shellBytes := by
  show contentOf (spaServedPath deployedSpaCfg (segsOf c.req.target)) = _
  rw [spaServedPath_index, contentOf_indexPath]

/-- **No escape, deployed**: the served path keeps the `app` root as a prefix even
under a `..`-popping walker — the model's no-escape, instantiated (root and index
are dot-free by kernel decision). -/
theorem deployed_no_escape (raw : List String) :
    deployedSpaCfg.docRoot <+: Route.Path.descend [] (spaServedPath deployedSpaCfg raw) :=
  spa_fallback_no_escape deployedSpaCfg raw
    (by intro s hs
        have h := List.mem_singleton.mp hs
        subst h
        decide)
    (by intro s hs
        have h := List.mem_singleton.mp hs
        subst h
        decide)

/-! ## Gate / stamp behaviour -/

theorem spaGate_fires (c : Ctx) (hm : c.req.method = getBytes)
    (ht : spaPrefix.isPrefixOf c.req.target = true) :
    spaGateStage.onRequest c = .respond (spaRespOf c) := by
  show (if inScope c then StageStep.respond (spaRespOf c) else StageStep.continue c) = _
  rw [inScope_true c hm ht]
  rfl

theorem spaGate_passes (c : Ctx) (h : spaPrefix.isPrefixOf c.req.target = false) :
    spaGateStage.onRequest c = .continue c := by
  show (if inScope c then StageStep.respond (spaRespOf c) else StageStep.continue c) = _
  rw [inScope_false_of_prefix c h]
  rfl

theorem spaGate_statusStable : Stage.statusStable spaGateStage := fun _ _ => rfl

/-- **The stamp's byte-effect.** On `GET /app/…` the finalized pipeline is the
tail's with the `text/html` pair appended — for ANY tail/handler. -/
theorem spaTypeStage_effect (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) (hm : c.req.method = getBytes)
    (ht : spaPrefix.isPrefixOf c.req.target = true) :
    runPipeline (spaTypeStage :: rest) h c
      = (runPipeline rest h c).addHeader (ctName, htmlVal) := by
  rw [pipeline_stage_effect spaTypeStage rest h c c rfl]
  show (if inScope c then (runPipeline rest h c).addHeader (ctName, htmlVal)
        else runPipeline rest h c) = _
  rw [inScope_true c hm ht]
  rfl

theorem spaTypeStage_noop (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) (ht : spaPrefix.isPrefixOf c.req.target = false) :
    runPipeline (spaTypeStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect spaTypeStage rest h c c rfl]
  show (if inScope c then (runPipeline rest h c).addHeader (ctName, htmlVal)
        else runPipeline rest h c) = _
  rw [inScope_false_of_prefix c ht]
  rfl

theorem spaTypeStage_statusStable : Stage.statusStable spaTypeStage := by
  intro c b
  show ((if inScope c then b.addHeader (ctName, htmlVal) else b).build).status
       = b.build.status
  by_cases h : inScope c = true
  · rw [if_pos h]; rfl
  · rw [if_neg h]

end Reactor.Stage.SpaServe

#print axioms Reactor.Stage.SpaServe.spa_resolved_not_file
#print axioms Reactor.Stage.SpaServe.spa_always_index
#print axioms Reactor.Stage.SpaServe.spaRespOf_body
#print axioms Reactor.Stage.SpaServe.deployed_no_escape
#print axioms Reactor.Stage.SpaServe.spaGate_fires
#print axioms Reactor.Stage.SpaServe.spaTypeStage_effect
