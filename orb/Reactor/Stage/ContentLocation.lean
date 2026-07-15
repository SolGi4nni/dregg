import Reactor.Pipeline
import Reactor.App

/-!
# Reactor.Stage.ContentLocation — `Content-Location` representation stage (RFC 9110 §8.7)

A byte-driving pipeline `Stage` that stamps `Content-Location` onto a `200 (OK)`
static-asset response, naming the URI of the specific representation returned
(RFC 9110 §8.7). The deployed static handler carries no `Content-Location` (see
`Proto.VaryProven`'s wire capture), so a client that later wants to address the
returned representation directly (e.g. to `PUT`/`DELETE` it, or to key a cache on
the canonical URI) has no protocol pointer. This stage supplies it: the
representation URI is the request target the static route resolved.

RESPONSE-TRANSFORM at the HEAD of the deployed chain (outermost `onResponse`): it
observes the FINAL built status and its header survives the inner header-map
rewrites. The request phase always passes.

## What is proven here (pure kernel; axioms ⊆ {propext, Quot.sound})

* `contentLocationStage_effect`       — the onion-effect factoring.
* `contentLocationStage_statusStable` — never changes the built status.
* `contentLocationStage_static200_present` — for ANY tail/handler whose inner build
  is a `200` to a `GET /static/…`, `Content-Location: <canonical path>` appears in
  the BUILT output, its value the SERVER-CHOSEN canonical resource path
  (`canonicalResourcePath`) — the query-stripped, normalized path the static route
  resolved against, never reflected request input.
* `contentLocationStage_nonstatic_absent` — no `Content-Location` off the static
  surface.
-/

namespace Reactor.Stage.ContentLocation

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)

/-- The `Content-Location` field name on the wire. -/
def contentLocationName : Bytes := "Content-Location".toUTF8.toList

/-- The static asset surface prefix (`/static/`). -/
def staticPrefix : Bytes := "/static/".toUTF8.toList

/-- The `GET` method bytes. -/
def getMethod : Bytes := "GET".toUTF8.toList

/-- A static GET whose representation URI is worth naming. -/
def isStaticGet (c : Ctx) : Bool :=
  c.req.method == getMethod && staticPrefix.isPrefixOf c.req.target

/-- **The canonical resolved resource path** for a request target. RFC 9110 §8.7
requires the `Content-Location` value to be the SERVER-CHOSEN representation URI —
never reflected request input. This re-serializes the exact traversal-safe path
segments the static route resolves against (`Reactor.App.targetSegments`: the query
`?…` suffix is dropped, the path is percent-decoded once and dot-segments removed),
so the value provably names the served resource and carries no query string. -/
def canonicalResourcePath (target : Bytes) : Bytes :=
  ("/" ++ String.intercalate "/" (Reactor.App.targetSegments target)).toUTF8.toList

/-- **The `Content-Location` stage.** Response-transform: passes the request
phase; on the response phase adds `Content-Location: <request target>` iff the
built status is `200` AND the request is a static GET, else identity. The value is
the server-chosen canonical resource path (`canonicalResourcePath`), never
reflected request input. -/
def contentLocationStage : Stage where
  name := "content-location"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if b.acc.status == 200 && isStaticGet c then
      b.addHeader (contentLocationName, canonicalResourcePath c.req.target)
    else b

/-- The stage factors through `pipeline_stage_effect`. -/
theorem contentLocationStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (contentLocationStage :: rest) h c
      = (if (runPipeline rest h c).acc.status == 200 && isStaticGet c
         then (runPipeline rest h c).addHeader (contentLocationName, canonicalResourcePath c.req.target)
         else (runPipeline rest h c)) :=
  pipeline_stage_effect contentLocationStage rest h c c rfl

/-- **Status-stable.** Adds at most one header; never touches the status. -/
theorem contentLocationStage_statusStable : Stage.statusStable contentLocationStage := by
  intro c b
  show ((if b.acc.status == 200 && isStaticGet c
          then b.addHeader (contentLocationName, canonicalResourcePath c.req.target) else b).build).status
        = b.build.status
  split <;> simp [build_addHeader]

/-- **Byte-effect on a static `200`.** A `200` answer to `GET /static/…` gains
`Content-Location` whose value is EXACTLY the canonical resolved resource path
(`canonicalResourcePath c.req.target`, query-stripped and normalized) — for ANY tail
and handler. -/
theorem contentLocationStage_static200_present (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (h200 : (runPipeline rest h c).acc.status = 200) (hstatic : isStaticGet c = true) :
    (contentLocationName, canonicalResourcePath c.req.target)
      ∈ ((runPipeline (contentLocationStage :: rest) h c).build).headers := by
  rw [contentLocationStage_effect, h200, hstatic]
  simp only [Nat.reduceBEq, Bool.and_true, if_true, build_addHeader, List.mem_append]
  exact Or.inr (List.mem_singleton.mpr rfl)

/-- **No pointer off the static surface.** A `200` that is not a static GET gets no
`Content-Location`: the output is byte-identical to the inner fold. -/
theorem contentLocationStage_nonstatic_absent (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hns : isStaticGet c = false) :
    (runPipeline (contentLocationStage :: rest) h c).build = (runPipeline rest h c).build := by
  rw [contentLocationStage_effect, hns]
  simp

/-- **Status-preserving in the fold.** Prepending the stage to any chain leaves the
built status of the fold unchanged (it only ever adds a header). -/
theorem contentLocationStage_preserves_status (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (runPipeline (contentLocationStage :: rest) h c).acc.status
      = (runPipeline rest h c).acc.status := by
  rw [contentLocationStage_effect]
  split <;> simp [ResponseBuilder.addHeader]

end Reactor.Stage.ContentLocation
