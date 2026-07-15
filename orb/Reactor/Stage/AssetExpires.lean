import Reactor.Pipeline
import Reactor.Stage.CacheControl

/-!
# Reactor.Stage.AssetExpires — the `Expires` freshness date for static assets (RFC 9111 §5.3)

A byte-driving pipeline `Stage` that stamps an explicit `Expires` field onto a
`200 (OK)` for a cacheable static asset. The deployed static handler answers
`GET /static/…` with a `Cache-Control` freshness lifetime
(`public, max-age=3600`) but NO `Expires`: an HTTP/1.0-only cache that does not
understand `Cache-Control: max-age` has no absolute freshness date to work from
and must revalidate every time (RFC 9111 §4.2.1 fallback). This stage closes that
edge — the origin names an absolute expiry so an HTTP/1.0 cache can compute
freshness (RFC 9111 §5.3).

The `Expires` value is an ABSOLUTE HTTP-date (RFC 9110 §5.6.7 IMF-fixdate), not a
relative lifetime, so it is a pure CONSTANT — no clock effect is needed. A cache
that ALSO understands `max-age` MUST prefer `max-age` and ignore `Expires`
(RFC 9111 §5.3), so the two directives coexist without conflict; `Expires`
therefore only widens compatibility, it never overrides the `max-age` lifetime.
It applies ONLY to the cacheable static surface.

RESPONSE-TRANSFORM at the HEAD of the deployed chain (outermost `onResponse`): it
observes the FINAL built status and its stamped date survives the inner header-map
rewrites. The request phase always passes, so the stage is the identity on every
non-static request (the dense `/bulk` datapath included).

## What is proven here (pure kernel; axioms ⊆ {propext, Quot.sound})

* `assetExpiresStage_effect`       — the onion-effect factoring.
* `assetExpiresStage_statusStable` — never changes the built status.
* `assetExpiresStage_static200_present` — for ANY tail/handler whose inner build is
  a `200` to a `GET /static/…`, the `Expires` date appears in the BUILT output.
* `assetExpiresStage_resp_off_static` — off the static surface the response phase is
  the identity ON THE BUILDER (the collapse fact the deployed pipeline consumes to
  keep the dense `/bulk` arm byte-identical).
* `assetExpiresStage_nonstatic_absent` — a `200` off the static surface gets NO
  `Expires`.
-/

namespace Reactor.Stage.AssetExpires

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)
open Reactor.Stage.CacheControl (isStaticGet)

/-- The `Expires` field name on the wire. -/
def expiresName : Bytes := "Expires".toUTF8.toList

/-- The deployed absolute expiry — a far-future IMF-fixdate
(`Thu, 31 Dec 2037 23:59:59 GMT`, RFC 9110 §5.6.7). A constant, not caller input;
`max-age` still governs for a cache that understands it (RFC 9111 §5.3). -/
def expiresVal : Bytes := "Thu, 31 Dec 2037 23:59:59 GMT".toUTF8.toList

/-- **The `Expires` stage.** Response-transform: passes the request phase; on the
response phase adds `Expires: <far-future>` iff the built status is `200` AND the
request is a cacheable static GET, else identity. -/
def assetExpiresStage : Stage where
  name := "asset-expires"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if b.acc.status == 200 && isStaticGet c then
      b.addHeader (expiresName, expiresVal)
    else b

/-- The stage factors through `pipeline_stage_effect`. -/
theorem assetExpiresStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (assetExpiresStage :: rest) h c
      = (if (runPipeline rest h c).acc.status == 200 && isStaticGet c
         then (runPipeline rest h c).addHeader (expiresName, expiresVal)
         else (runPipeline rest h c)) :=
  pipeline_stage_effect assetExpiresStage rest h c c rfl

/-- **Status-stable.** Adds at most one header; never touches the status. -/
theorem assetExpiresStage_statusStable : Stage.statusStable assetExpiresStage := by
  intro c b
  show ((if b.acc.status == 200 && isStaticGet c
          then b.addHeader (expiresName, expiresVal) else b).build).status
        = b.build.status
  split <;> simp [build_addHeader]

/-- **Byte-effect on a static `200`.** A `200` answer to `GET /static/…` gains its
absolute `Expires` date — for ANY tail and handler. -/
theorem assetExpiresStage_static200_present (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (h200 : (runPipeline rest h c).acc.status = 200) (hstatic : isStaticGet c = true) :
    (expiresName, expiresVal)
      ∈ ((runPipeline (assetExpiresStage :: rest) h c).build).headers := by
  rw [assetExpiresStage_effect, h200, hstatic]
  simp only [Nat.reduceBEq, Bool.and_true, if_true, build_addHeader, List.mem_append]
  exact Or.inr (List.mem_singleton.mpr rfl)

/-- **Off the static surface the response phase is the identity ON THE BUILDER.**
The collapse fact the deployed pipeline consumes: a request that is not a static
GET is untouched, so the dense `/bulk` arm stays byte-identical. -/
theorem assetExpiresStage_resp_off_static (c : Ctx) (b : ResponseBuilder)
    (hns : isStaticGet c = false) :
    assetExpiresStage.onResponse c b = b := by
  show (if b.acc.status == 200 && isStaticGet c
        then b.addHeader (expiresName, expiresVal) else b) = b
  rw [hns]; simp

/-- **No date off the static surface.** A `200` that is not a static GET gets NO
`Expires`: the output is byte-identical to the inner fold. -/
theorem assetExpiresStage_nonstatic_absent (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hns : isStaticGet c = false) :
    (runPipeline (assetExpiresStage :: rest) h c).build = (runPipeline rest h c).build := by
  rw [assetExpiresStage_effect, hns]
  simp

end Reactor.Stage.AssetExpires

#print axioms Reactor.Stage.AssetExpires.assetExpiresStage_static200_present
#print axioms Reactor.Stage.AssetExpires.assetExpiresStage_resp_off_static
#print axioms Reactor.Stage.AssetExpires.assetExpiresStage_statusStable
