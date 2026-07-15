import Reactor.Pipeline
import Reactor.Stage.CacheControl

/-!
# Reactor.Stage.AssetImmutable — `Cache-Control: immutable` for static assets (RFC 8246)

A byte-driving pipeline `Stage` that stamps the `immutable` cache-response
directive (RFC 8246) onto a `200 (OK)` for a cacheable static asset. The deployed
static handler answers `GET /static/…` with an `ETag` + a `Cache-Control`
freshness lifetime (`public, max-age=3600`, from `Reactor.Stage.CacheControl`), but
NO `immutable` directive: a fresh cached response is still revalidated on a user
reload. This stage closes that edge — a content-addressed static asset never
changes for its URL, so the origin promises the stored representation will not be
updated during its freshness lifetime, and a conditional revalidation on reload is
avoided (RFC 8246 §2).

`immutable` is a `Cache-Control` extension directive (RFC 9111 §5.2.3): it is
carried as an additional `Cache-Control` field line, which combines with the
existing freshness directive as if comma-concatenated (RFC 9110 §5.3). It applies
ONLY to the cacheable static surface — a dynamic representation may change and must
not be marked immutable.

RESPONSE-TRANSFORM at the HEAD of the deployed chain (outermost `onResponse`): it
observes the FINAL built status and its stamped directive survives the inner
header-map rewrites. The request phase always passes, so the stage is the identity
on every non-static request (the dense `/bulk` datapath included).

## What is proven here (pure kernel; axioms ⊆ {propext, Quot.sound})

* `assetImmutableStage_effect`       — the onion-effect factoring.
* `assetImmutableStage_statusStable` — never changes the built status.
* `assetImmutableStage_static200_present` — for ANY tail/handler whose inner build
  is a `200` to a `GET /static/…`, the `immutable` directive appears in the BUILT
  output.
* `assetImmutableStage_resp_off_static` — off the static surface the response phase
  is the identity ON THE BUILDER (the collapse fact the deployed pipeline consumes
  to keep the dense `/bulk` arm byte-identical).
* `assetImmutableStage_nonstatic_absent` — a `200` off the static surface gets NO
  `immutable` directive.
-/

namespace Reactor.Stage.AssetImmutable

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)
open Reactor.Stage.CacheControl (isStaticGet)

/-- The `Cache-Control` field name on the wire (the extension rides its own line). -/
def immutableName : Bytes := "Cache-Control".toUTF8.toList

/-- The `immutable` cache-response extension directive (RFC 8246 §2). A constant,
not caller input. -/
def immutableVal : Bytes := "immutable".toUTF8.toList

/-- **The `immutable` stage.** Response-transform: passes the request phase; on the
response phase adds `Cache-Control: immutable` iff the built status is `200` AND the
request is a cacheable static GET, else identity. -/
def assetImmutableStage : Stage where
  name := "asset-immutable"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    if b.acc.status == 200 && isStaticGet c then
      b.addHeader (immutableName, immutableVal)
    else b

/-- The stage factors through `pipeline_stage_effect`. -/
theorem assetImmutableStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (assetImmutableStage :: rest) h c
      = (if (runPipeline rest h c).acc.status == 200 && isStaticGet c
         then (runPipeline rest h c).addHeader (immutableName, immutableVal)
         else (runPipeline rest h c)) :=
  pipeline_stage_effect assetImmutableStage rest h c c rfl

/-- **Status-stable.** Adds at most one header; never touches the status. -/
theorem assetImmutableStage_statusStable : Stage.statusStable assetImmutableStage := by
  intro c b
  show ((if b.acc.status == 200 && isStaticGet c
          then b.addHeader (immutableName, immutableVal) else b).build).status
        = b.build.status
  split <;> simp [build_addHeader]

/-- **Byte-effect on a static `200`.** A `200` answer to `GET /static/…` gains the
`immutable` directive — for ANY tail and handler. -/
theorem assetImmutableStage_static200_present (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (h200 : (runPipeline rest h c).acc.status = 200) (hstatic : isStaticGet c = true) :
    (immutableName, immutableVal)
      ∈ ((runPipeline (assetImmutableStage :: rest) h c).build).headers := by
  rw [assetImmutableStage_effect, h200, hstatic]
  simp only [Nat.reduceBEq, Bool.and_true, if_true, build_addHeader, List.mem_append]
  exact Or.inr (List.mem_singleton.mpr rfl)

/-- **Off the static surface the response phase is the identity ON THE BUILDER.**
The collapse fact the deployed pipeline consumes: a request that is not a static
GET is untouched, so the dense `/bulk` arm stays byte-identical. -/
theorem assetImmutableStage_resp_off_static (c : Ctx) (b : ResponseBuilder)
    (hns : isStaticGet c = false) :
    assetImmutableStage.onResponse c b = b := by
  show (if b.acc.status == 200 && isStaticGet c
        then b.addHeader (immutableName, immutableVal) else b) = b
  rw [hns]; simp

/-- **No directive off the static surface.** A `200` that is not a static GET gets
NO `immutable`: the output is byte-identical to the inner fold. -/
theorem assetImmutableStage_nonstatic_absent (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hns : isStaticGet c = false) :
    (runPipeline (assetImmutableStage :: rest) h c).build = (runPipeline rest h c).build := by
  rw [assetImmutableStage_effect, hns]
  simp

end Reactor.Stage.AssetImmutable

#print axioms Reactor.Stage.AssetImmutable.assetImmutableStage_static200_present
#print axioms Reactor.Stage.AssetImmutable.assetImmutableStage_resp_off_static
#print axioms Reactor.Stage.AssetImmutable.assetImmutableStage_statusStable
