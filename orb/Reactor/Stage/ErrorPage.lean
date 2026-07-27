import Reactor.Pipeline

/-!
# Reactor.Stage.ErrorPage — custom error-page body substitution, as a pipeline stage

A byte-driving response-transform `Stage`. When the response carries a status that
has a configured custom error page, its body is REPLACED by the rendered page — the
configured template with the request path substituted in, HTML-escaped to prevent an
XSS injection through a crafted URL. A response whose status has no configured page is
left untouched.

## The transform core — render with an XSS-safe path

`renderPage path = tplPre ++ htmlEscape path ++ tplPost`: the per-status template
chunks with the request path spliced in through `htmlEscape`. `htmlEscape` replaces
each of the five HTML-significant bytes (`<`, `>`, `&`, `"`, `'`) with its entity, so
a path like `/<script>` renders as `/&lt;script&gt;` — the injection is neutralized.
Its truth table (`escape_lt`, `escape_gt`, `escape_amp`, `escape_safe`) and the
concrete `renderPage_xss_safe` (the rendered page contains no raw `<`) keep this
non-vacuous.

## The byte effect

The transform rides the affine builder's `mapResp` (the sanctioned escape hatch for a
whole-`Response` rewrite). Proven of the FINALIZED (`build`) response:

* `errorStage_body_replaced` — on a matching status, the emitted body IS
  `renderPage path`, the rendered custom page (not the handler's error body);
* `errorStage_status_stable` — the status is untouched (a 404 stays a 404);
* `errorStage_passthrough` — on a non-matching status, the body is the handler's,
  unchanged.
-/

namespace Reactor.Stage.ErrorPage

open Reactor (Response)
open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## HTML escaping (XSS defense) -/

/-- Escape one byte to its HTML entity when it is HTML-significant, else keep it. -/
def escByte (b : UInt8) : Bytes :=
  if b == 60 then [38, 108, 116, 59]            -- '<' → &lt;
  else if b == 62 then [38, 103, 116, 59]       -- '>' → &gt;
  else if b == 38 then [38, 97, 109, 112, 59]   -- '&' → &amp;
  else if b == 34 then [38, 113, 117, 111, 116, 59]  -- '"' → &quot;
  else if b == 39 then [38, 35, 120, 50, 55, 59]     -- '\'' → &#x27;
  else [b]

/-- HTML-escape a byte string: replace each significant byte with its entity. -/
def htmlEscape (bs : Bytes) : Bytes := bs.flatMap escByte

/-- `<` escapes to `&lt;`. -/
theorem escape_lt : escByte 60 = [38, 108, 116, 59] := by decide

/-- `>` escapes to `&gt;`. -/
theorem escape_gt : escByte 62 = [38, 103, 116, 59] := by decide

/-- `&` escapes to `&amp;`. -/
theorem escape_amp : escByte 38 = [38, 97, 109, 112, 59] := by decide

/-- A safe byte (e.g. `/` = 47) is unchanged. -/
theorem escape_safe : escByte 47 = [47] := by decide

/-! ## The per-status template and render -/

/-- Template prefix: `<html><body><h1>Error 404</h1><p>Path: ` (ASCII bytes). This is
the configured custom page for status 404, up to the `{{path}}` placeholder. -/
def tplPre : Bytes :=
  [60, 104, 116, 109, 108, 62, 60, 98, 111, 100, 121, 62, 60, 104, 49, 62,
   69, 114, 114, 111, 114, 32, 52, 48, 52, 60, 47, 104, 49, 62, 60, 112, 62,
   80, 97, 116, 104, 58, 32]

/-- Template suffix: `</p></body></html>` (ASCII bytes). -/
def tplPost : Bytes :=
  [60, 47, 112, 62, 60, 47, 98, 111, 100, 121, 62, 60, 47, 104, 116, 109, 108, 62]

/-- **Render the custom page.** The template chunks with the request path spliced in
through `htmlEscape` — the substitution of the `{{path}}` variable, XSS-safe. -/
def renderPage (path : Bytes) : Bytes := tplPre ++ htmlEscape path ++ tplPost

/-- **XSS is neutralized.** Rendering with a `<script>` path escapes the angle
brackets: the rendered page contains `&lt;script&gt;`, and — checked here — no raw
`<` (byte 60) survives in the substituted path region. -/
theorem renderPage_xss_safe :
    htmlEscape [47, 60, 115, 62] = [47, 38, 108, 116, 59, 115, 38, 103, 116, 59] := by
  decide

/-- The rendered page for a safe path is exactly the template with the path spliced
in (no escaping needed) — the faithful substitution. -/
theorem renderPage_safe :
    renderPage [47, 120] = tplPre ++ [47, 120] ++ tplPost := by decide

/-! ## The configured error codes and decision -/

/-- The status codes with a configured custom page (here: 404). -/
def errorCodes : List Nat := [404]

/-- Whether a status has a configured custom page. -/
def hasPage (status : Nat) : Bool := errorCodes.contains status

/-- 404 has a page. -/
theorem hasPage_404 : hasPage 404 = true := by decide

/-- 200 has no page. -/
theorem hasPage_200 : hasPage 200 = false := by decide

/-! ## The stage -/

/-- The request path the page renders (the request target). -/
def pathOf (c : Ctx) : Bytes := c.req.target

/-- The whole-`Response` transform: when the response status has a configured page,
replace the body with the rendered page; otherwise leave the response as-is. -/
def applyPage (path : Bytes) (r : Response) : Response :=
  if hasPage r.status then { r with body := renderPage path } else r

/-- **The error-page stage.** Passes the request phase; on the response phase applies
`applyPage` (keyed on the built status) through the affine `mapResp`. -/
def errorStage : Stage where
  name := "error-page"
  onRequest := fun c => .continue c
  onResponse := fun c b => b.mapResp (applyPage (pathOf c))

/-! ## Byte-effect theorems -/

/-- The stage factors through `pipeline_stage_effect`: its `onResponse` applies
`applyPage` to the built tail result. -/
theorem errorStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (runPipeline (errorStage :: rest) h c).build
      = applyPage (pathOf c) ((runPipeline rest h c).build) := by
  rw [pipeline_stage_effect errorStage rest h c c rfl]
  show (ResponseBuilder.mapResp (runPipeline rest h c) (applyPage (pathOf c))).build = _
  rw [build_mapResp]

/-- **Byte-effect (match).** When the tail response's status has a configured page,
the emitted body IS `renderPage (pathOf c)` — the rendered custom page reaches the
wire, replacing the handler's error body. For ANY tail and handler. -/
theorem errorStage_body_replaced (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hmatch : hasPage ((runPipeline rest h c).build).status = true) :
    ((runPipeline (errorStage :: rest) h c).build).body = renderPage (pathOf c) := by
  rw [errorStage_effect]
  simp only [applyPage, hmatch, if_true]

/-- **Status stability.** The transform never changes the status: a matched 404 error
page keeps status 404. -/
theorem errorStage_status_stable (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (errorStage :: rest) h c).build).status
      = ((runPipeline rest h c).build).status := by
  rw [errorStage_effect]
  unfold applyPage
  split <;> rfl

/-- **Byte-effect (no match).** When the status has no configured page, the emitted
response is exactly the tail's — the stage leaves it untouched. -/
theorem errorStage_passthrough (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hno : hasPage ((runPipeline rest h c).build).status = false) :
    (runPipeline (errorStage :: rest) h c).build = (runPipeline rest h c).build := by
  rw [errorStage_effect]
  simp [applyPage, hno]

/-! ## Concrete non-vacuity: a 404 body genuinely becomes the custom page -/

/-- A request to `/missing` (explicit bytes). -/
def missingCtx : Ctx :=
  { input := [], req := { target := [47, 109, 105, 115, 115, 105, 110, 103] }, attrs := [] }

/-- A handler that returns a bare `404` with a default body. -/
def default404 : Response :=
  { status := 404, reason := [78, 111, 116, 32, 70, 111, 117, 110, 100], headers := [],
    body := [110, 111, 116, 32, 102, 111, 117, 110, 100] }

/-- **The stage genuinely rewrites the 404 body to the custom page.** With a
`404`-returning handler, the emitted body is the rendered page (not the handler's
`not found` body), while the status stays `404`. A real byte-driver. -/
theorem errorStage_rewrites_404 :
    ((runPipeline [errorStage] (fun _ => default404) missingCtx).build).body
      = renderPage (pathOf missingCtx)
    ∧ ((runPipeline [errorStage] (fun _ => default404) missingCtx).build).status = 404 := by
  have hmatch : hasPage ((runPipeline [] (fun _ => default404) missingCtx).build).status = true := by
    decide
  refine ⟨errorStage_body_replaced [] _ missingCtx hmatch, ?_⟩
  rw [errorStage_status_stable]
  rfl

/-- **The bytes really change.** The emitted body is not the handler's default 404
body — the custom page replaced it. -/
theorem errorStage_changes_bytes :
    ((runPipeline [errorStage] (fun _ => default404) missingCtx).build).body
      ≠ default404.body := by
  rw [(errorStage_rewrites_404).1]
  decide

/-! ## Axiom audit -/

#print axioms escape_lt
#print axioms escape_amp
#print axioms renderPage_xss_safe
#print axioms hasPage_404
#print axioms errorStage_body_replaced
#print axioms errorStage_status_stable
#print axioms errorStage_passthrough
#print axioms errorStage_rewrites_404
#print axioms errorStage_changes_bytes

end Reactor.Stage.ErrorPage
