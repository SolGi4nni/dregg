import Reactor.Pipeline

/-!
# Reactor.Stage.Dashboard — the deployed live-serve dashboard page

The admin surface had probes (`/health`, the SSE `/events` burst, `/metrics`
behind the operator listener) but NO dashboard: no single page an operator
opens to watch the serve. This module builds the missing feature as the
`GET /dashboard` route serving a self-refreshing HTML page that live-embeds
the deployed probes:

* the page `<meta http-equiv="refresh" content="5">`-refreshes itself — no
  inline script, so it renders fully under the deployed strict
  `Content-Security-Policy` (script-less by construction);
* the health probe and the SSE event burst are embedded LIVE as same-origin
  `<iframe>`s (each refresh re-fetches them through the real serve);
* the deployed routes (login, SPA shell, static, bulk, welcome) are linked
  for one-click probing.

Two stages, the `SpaServe` geometry:

* `dashGateStage` — request-phase gate: `GET /dashboard` ⇒ the `200` shell.
* `dashTypeStage` — response-phase stamp: on `GET /dashboard`, push
  `Content-Type: text/html`. OUTSIDE the rewrite onion, so the header-less
  gate seed keeps the deployed content-type-gated body rewrite a passthrough
  while the wire still declares the page HTML.

## What is proven (pure kernel)

* `dashGate_fires` / `dashGate_passes` — the gate answers exactly its scope.
* `dashTypeStage_effect` / `dashTypeStage_noop` — the stamp appends exactly
  `(Content-Type, text/html)` in scope, identity off it.
* `shell_embeds_health` / `shell_embeds_events` — the served shell GENUINELY
  embeds the two live probes (structural infix facts on the byte level — the
  page is a dashboard OF the running serve, not a static brochure).
* Status-stability of both stages.

Named residuals (honest): the refresh is whole-page (`meta refresh`), not a
per-fragment swap engine; the metrics table stays behind the operator
listener (linking it here would 401 without the operator's token).
-/

namespace Reactor.Stage.Dashboard

open Reactor.Pipeline
open Proto (Bytes)

/-- ASCII `"GET"`. -/
def getBytes : Bytes := [71, 69, 84]

/-- ASCII `"/dashboard"` — the dashboard route. -/
def dashTarget : Bytes := [47, 100, 97, 115, 104, 98, 111, 97, 114, 100]

/-- ASCII `"Content-Type"`. -/
def ctName : Bytes := [67, 111, 110, 116, 101, 110, 116, 45, 84, 121, 112, 101]

/-- ASCII `"text/html"`. -/
def htmlVal : Bytes := [116, 101, 120, 116, 47, 104, 116, 109, 108]

/-- ASCII `"OK"`. -/
def okReason : Bytes := [79, 75]

/-! ## The shell (an explicit concatenation, so the live-probe embeddings are
structural facts, not opaque substring searches) -/

/-- The shell head: self-refreshing, script-less (CSP-clean by construction). -/
def preBytes : Bytes :=
  "<!doctype html><html><head><«meta» charset=\"utf-8\"><«meta» http-equiv=\"refresh\" content=\"5\"><title>drorb dashboard</title><style>body{font-family:monospace;margin:2em}iframe{border:1px solid #888;width:22em;height:4em}section{margin-bottom:1em}</style></head><body><h1>drorb live serve dashboard</h1><p>auto-refreshes every 5s; script-less (CSP-clean).</p><section><h2>health</h2>".toUTF8.toList

/-- The LIVE health probe embed. -/
def healthProbe : Bytes :=
  "<iframe src=\"/health\" title=\"health\"></iframe>".toUTF8.toList

/-- Between the probes. -/
def midBytes : Bytes :=
  "</section><section><h2>event burst (proven SSE framing)</h2>".toUTF8.toList

/-- The LIVE event-stream probe embed. -/
def eventsProbe : Bytes :=
  "<iframe src=\"/events\" title=\"events\"></iframe>".toUTF8.toList

/-- The shell tail: one-click probes of the deployed routes. -/
def postBytes : Bytes :=
  "</section><nav><h2>routes</h2><a href=\"/login\">login (hardened cookie)</a> | <a href=\"/app/\">SPA shell</a> | <a href=\"/static/app.js\">static</a> | <a href=\"/bulk\">bulk (1 MiB)</a> | <a href=\"/welcome\">welcome (i18n)</a></nav></body></html>".toUTF8.toList

/-- **The dashboard shell.** -/
def shellBytes : Bytes :=
  preBytes ++ healthProbe ++ midBytes ++ eventsProbe ++ postBytes

/-- The served page GENUINELY embeds the live health probe. -/
theorem shell_embeds_health : healthProbe <:+: shellBytes :=
  ⟨preBytes, midBytes ++ eventsProbe ++ postBytes, by
    simp [shellBytes, List.append_assoc]⟩

/-- The served page GENUINELY embeds the live event-stream probe. -/
theorem shell_embeds_events : eventsProbe <:+: shellBytes :=
  ⟨preBytes ++ healthProbe ++ midBytes, postBytes, by
    simp [shellBytes, List.append_assoc]⟩

/-! ## The stages -/

/-- The route's guard: method `GET`, target `/dashboard`. -/
def inScope (c : Ctx) : Bool :=
  c.req.method == getBytes && c.req.target == dashTarget

/-- The dashboard's bare response: header-LESS seed (the media type is stamped
by `dashTypeStage` outside the rewrite onion), body the shell. -/
def dashResp : Reactor.Response :=
  { status := 200, reason := okReason, headers := [], body := shellBytes }

/-- **The dashboard gate.** Answers `GET /dashboard` with the shell; passes
everything else through untouched. -/
def dashGateStage : Stage where
  name := "dashboard"
  onRequest := fun c => if inScope c then .respond dashResp else .continue c
  onResponse := fun _ b => b

/-- **The dashboard media-type stamp.** Response phase: on `GET /dashboard`,
push `Content-Type: text/html`; identity elsewhere. -/
def dashTypeStage : Stage where
  name := "dashboard-type"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if inScope c then b.addHeader (ctName, htmlVal) else b

/-! ## The guard -/

theorem inScope_true (c : Ctx) (hm : c.req.method = getBytes)
    (ht : c.req.target = dashTarget) : inScope c = true := by
  unfold inScope
  rw [hm, ht]
  rfl

theorem inScope_false_of_target (c : Ctx) (h : ¬ c.req.target = dashTarget) :
    inScope c = false := by
  unfold inScope
  have hf : (c.req.target == dashTarget) = false := by
    cases hb : c.req.target == dashTarget
    · rfl
    · exact absurd (eq_of_beq hb) h
  rw [hf, Bool.and_false]

/-! ## Gate behaviour -/

/-- The gate fires on `GET /dashboard`. -/
theorem dashGate_fires (c : Ctx) (hm : c.req.method = getBytes)
    (ht : c.req.target = dashTarget) :
    dashGateStage.onRequest c = .respond dashResp := by
  show (if inScope c then StageStep.respond dashResp
        else StageStep.continue c) = _
  rw [inScope_true c hm ht]
  rfl

/-- The gate passes any non-dashboard target through untouched. -/
theorem dashGate_passes (c : Ctx) (h : ¬ c.req.target = dashTarget) :
    dashGateStage.onRequest c = .continue c := by
  show (if inScope c then StageStep.respond dashResp
        else StageStep.continue c) = _
  rw [inScope_false_of_target c h]
  rfl

theorem dashGate_statusStable : Stage.statusStable dashGateStage :=
  fun _ _ => rfl

/-! ## Stamp behaviour -/

/-- **The stamp's byte-effect.** On `GET /dashboard` the finalized pipeline is
the tail's with `(Content-Type, text/html)` appended — for ANY tail/handler. -/
theorem dashTypeStage_effect (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) (hm : c.req.method = getBytes) (ht : c.req.target = dashTarget) :
    runPipeline (dashTypeStage :: rest) h c
      = (runPipeline rest h c).addHeader (ctName, htmlVal) := by
  rw [pipeline_stage_effect dashTypeStage rest h c c rfl]
  show (if inScope c then (runPipeline rest h c).addHeader (ctName, htmlVal)
        else runPipeline rest h c) = _
  rw [inScope_true c hm ht]
  rfl

/-- Off the dashboard target the stamp is the identity. -/
theorem dashTypeStage_noop (rest : List Stage) (h : Ctx → Reactor.Response)
    (c : Ctx) (ht : ¬ c.req.target = dashTarget) :
    runPipeline (dashTypeStage :: rest) h c = runPipeline rest h c := by
  rw [pipeline_stage_effect dashTypeStage rest h c c rfl]
  show (if inScope c then (runPipeline rest h c).addHeader (ctName, htmlVal)
        else runPipeline rest h c) = _
  rw [inScope_false_of_target c ht]
  rfl

/-- The stamp never changes the built status (either branch). -/
theorem dashTypeStage_statusStable : Stage.statusStable dashTypeStage := by
  intro c b
  show ((if inScope c then b.addHeader (ctName, htmlVal) else b).build).status
       = b.build.status
  by_cases h : inScope c = true
  · rw [if_pos h]; rfl
  · rw [if_neg h]

/-! ## A concrete end-to-end witness -/

/-- A bare `GET /dashboard` context. -/
def dashCtx : Ctx :=
  { input := []
    req := { method := getBytes, target := dashTarget, version := [], headers := [] }
    attrs := [] }

/-- **The composed pair serves the typed shell**: gate + stamp answer the
dashboard context `200 text/html` with body exactly the shell. -/
theorem demo_dashboard :
    ((runPipeline [dashTypeStage, dashGateStage] (fun _ => dashResp) dashCtx).build).status
        = 200
  ∧ (ctName, htmlVal)
      ∈ ((runPipeline [dashTypeStage, dashGateStage] (fun _ => dashResp) dashCtx).build).headers
  ∧ ((runPipeline [dashTypeStage, dashGateStage] (fun _ => dashResp) dashCtx).build).body
        = shellBytes := by
  rw [dashTypeStage_effect [dashGateStage] (fun _ => dashResp) dashCtx rfl rfl,
      pipeline_gate_short_circuits dashGateStage [] (fun _ => dashResp) dashCtx
        dashResp (dashGate_fires dashCtx rfl rfl)]
  refine ⟨rfl, ?_, rfl⟩
  show (ctName, htmlVal) ∈ dashResp.headers ++ [(ctName, htmlVal)]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

end Reactor.Stage.Dashboard

#print axioms Reactor.Stage.Dashboard.shell_embeds_health
#print axioms Reactor.Stage.Dashboard.shell_embeds_events
#print axioms Reactor.Stage.Dashboard.dashGate_fires
#print axioms Reactor.Stage.Dashboard.dashTypeStage_effect
#print axioms Reactor.Stage.Dashboard.demo_dashboard
