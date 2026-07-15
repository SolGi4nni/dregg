import Reactor.Pipeline

/-!
# Reactor.Stage.CacheControl — origin `Cache-Control` freshness stage (RFC 9111 §5.2)

A byte-driving pipeline `Stage` that stamps an explicit `Cache-Control` freshness
directive onto a `200 (OK)` response for a cacheable static asset. The deployed
static handler answers `GET /static/…` with `ETag` + `Accept-Ranges` +
`Content-Type` but NO `Cache-Control` (see `Proto.VaryProven`'s wire capture): the
origin advertises no explicit freshness lifetime, so a shared cache must
heuristically guess (RFC 9111 §4.2.2) or always revalidate. This stage closes that
caching edge: the origin now names `public, max-age=3600` so downstream caches
have a deterministic freshness lifetime (RFC 9111 §5.2.2.1 `max-age`, §5.2.2.9
`public`).

RESPONSE-TRANSFORM at the HEAD of the deployed chain (outermost `onResponse`): it
observes the FINAL built status and its stamped directive survives the inner
header-map rewrites. The request phase always passes.

## What is proven here (pure kernel; axioms ⊆ {propext, Quot.sound})

* `cacheControlStage_effect`       — the onion-effect factoring.
* `cacheControlStage_statusStable` — never changes the built status.
* `cacheControlStage_static200_present` — for ANY tail/handler whose inner build is
  a `200` to a `GET /static/…`, the `Cache-Control` directive appears in the
  BUILT output.
* `cacheControlStage_nonstatic_absent` — a `200` off the static surface gets NO
  `Cache-Control` (only cacheable static assets are given a lifetime).
-/

namespace Reactor.Stage.CacheControl

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)

/-- The `Cache-Control` field name on the wire. -/
def cacheControlName : Bytes := "Cache-Control".toUTF8.toList

/-- The deployed freshness directive: `public, max-age=3600` — one hour of shared
cacheability (RFC 9111 §5.2.2.1 / §5.2.2.9). A constant, not caller input. -/
def cacheControlVal : Bytes := "public, max-age=3600".toUTF8.toList

/-- The static asset surface prefix (`/static/`) — the cacheable route family. -/
def staticPrefix : Bytes := "/static/".toUTF8.toList

/-- The `GET` method bytes. -/
def getMethod : Bytes := "GET".toUTF8.toList

/-- A cacheable static GET: method is `GET` and the target is under `/static/`. -/
def isStaticGet (c : Ctx) : Bool :=
  c.req.method == getMethod && staticPrefix.isPrefixOf c.req.target

/-- **The `Cache-Control` stage.** Response-transform: passes the request phase;
on the response phase adds `Cache-Control: public, max-age=3600` iff the built
status is `200` AND the request is a cacheable static GET, else identity. -/
def cacheControlStage : Stage where
  name := "cache-control"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if b.acc.status == 200 && isStaticGet c then
      b.addHeader (cacheControlName, cacheControlVal)
    else b

/-- The stage factors through `pipeline_stage_effect`. -/
theorem cacheControlStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (cacheControlStage :: rest) h c
      = (if (runPipeline rest h c).acc.status == 200 && isStaticGet c
         then (runPipeline rest h c).addHeader (cacheControlName, cacheControlVal)
         else (runPipeline rest h c)) :=
  pipeline_stage_effect cacheControlStage rest h c c rfl

/-- **Status-stable.** Adds at most one header; never touches the status. -/
theorem cacheControlStage_statusStable : Stage.statusStable cacheControlStage := by
  intro c b
  show ((if b.acc.status == 200 && isStaticGet c
          then b.addHeader (cacheControlName, cacheControlVal) else b).build).status
        = b.build.status
  split <;> simp [build_addHeader]

/-- **Byte-effect on a static `200`.** A `200` answer to `GET /static/…` gains its
explicit `Cache-Control` freshness directive — for ANY tail and handler. -/
theorem cacheControlStage_static200_present (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (h200 : (runPipeline rest h c).acc.status = 200) (hstatic : isStaticGet c = true) :
    (cacheControlName, cacheControlVal)
      ∈ ((runPipeline (cacheControlStage :: rest) h c).build).headers := by
  rw [cacheControlStage_effect, h200, hstatic]
  simp only [Nat.reduceBEq, Bool.and_true, if_true, build_addHeader, List.mem_append]
  exact Or.inr (List.mem_singleton.mpr rfl)

/-- **No lifetime off the static surface.** A `200` that is not a static GET gets
NO `Cache-Control`: the output is byte-identical to the inner fold. Only cacheable
static assets are given a freshness lifetime. -/
theorem cacheControlStage_nonstatic_absent (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hns : isStaticGet c = false) :
    (runPipeline (cacheControlStage :: rest) h c).build = (runPipeline rest h c).build := by
  rw [cacheControlStage_effect, hns]
  simp

/-- **Status-preserving in the fold.** Prepending the stage to any chain leaves the
built status of the fold unchanged (it only ever adds a header). Lets a composition
proof peel the stage off when reasoning about a downstream status (e.g. a `429`). -/
theorem cacheControlStage_preserves_status (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (runPipeline (cacheControlStage :: rest) h c).acc.status
      = (runPipeline rest h c).acc.status := by
  rw [cacheControlStage_effect]
  split <;> simp [ResponseBuilder.addHeader]

end Reactor.Stage.CacheControl
