import Datapath.ByteRefine
import Reactor.Deploy

/-!
# Datapath.FlatStage_errpage — the deployed `error-page` stage proven flat and
byte-identical to its `List`-typed form, for the cons-list removal.

The deployed stage is `Reactor.Deploy.errorPageBraidStage` (position in
`Reactor.Deploy.braidedChain2`): gated on the `x-error-page` marker, its response
phase delegates to the REAL library stage `Reactor.Stage.ErrorPage.errorStage`,
whose whole effect is `applyPage (pathOf c)` ridden through the affine `mapResp`.
`applyPage` is a BODY transform (not a header fold): on a status with a configured
custom page it REPLACES the body with `renderPage path`, otherwise it is the
identity. So — unlike the `securityheaders` exemplar (a header fold on `HdrBlock`)
— the cons-list this stage builds lives in the BODY bytes, and the flat form is
built with the byte grain (`Datapath.ByteRefine`), exactly as the ground-truth
scope directs ("body via ByteRefine if it sets a body").

The body the stage writes is `renderPage path = tplPre ++ htmlEscape path ++ tplPost`
— a `List.++` chain whose middle fragment `htmlEscape path = path.flatMap escByte`
is itself a per-byte `flatMap` cons-build. BOTH cons-lists are removed here.

## What is proven (equality-transfer / byte-identity, NOT a re-spec)

* `errorStage_resp_effect` / `errorBraid_resp_effect` — the DEPLOYED effect,
  grounded: the built response of the real `errorStage.onResponse` (and of the
  deployed `errorPageBraidStage.onResponse` when the marker is present) is exactly
  `applyPage (pathOf c) b.build`, read off the stage via `build_mapResp`. This is
  the function the flat form must compute; we do not re-specify it.
* `flatHtmlEscape` + `flatHtmlEscape_refines` — the flat XSS escape: a flat
  accumulator fold (`foldAppend`, amortized-`O(1)` push, no per-byte cons-spine)
  proven byte-identical to `htmlEscape` via the FOLD combinator `refine_fold`.
* `flatRenderPage` + `flatRenderPage_refines` — the flat rendered page, built from
  the `++` combinator (`refine_append`) over the template chunks with the flat
  escaped path spliced in, proven byte-identical to `renderPage` (`Refines`).
* `flatApplyPage` + `flatApplyPage_eq` — the flat whole-`Response` transform,
  proven EQUAL to the deployed `applyPage` (the body equality transferred through
  the `if`), and `flatApplyPage_eq_stage` ties it to the real `errorStage`.
* `flatError_serialize_refines` — THE FULL BYTE-IDENTITY: the flat stage's whole
  serialized response (flat body build ⟶ `Datapath.ByteRefine.flatSerialize`) is
  byte-identical to `Reactor.serialize` of the DEPLOYED stage's response, chaining
  the body equality into the byte-grain `flatSerialize_refines`.

The single `.toList` at the `Response.body` field boundary (the deployed `Response`
is `List`-typed) is the named residual seam — the exact analogue of the exemplar's
header `denote` seam; the body accumulation and the serialization are both flat.
-/

namespace Datapath.FlatStageErrpage

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx ResponseBuilder build_mapResp)
open Reactor.Stage.ErrorPage
  (errorStage applyPage renderPage htmlEscape escByte tplPre tplPost hasPage pathOf
   missingCtx default404)
open Datapath.Refinement

/-! ## 1. The deployed stage's response effect, read off the REAL stages -/

/-- **The library `error-page` stage's built effect — grounded, not re-specified.**
The BUILT response of the real `errorStage.onResponse` is `applyPage (pathOf c)`
applied to the built base, read directly off the stage (its `onResponse` is
`b.mapResp (applyPage (pathOf c))`) via `build_mapResp`. This is the function the
flat form must compute. -/
theorem errorStage_resp_effect (c : Ctx) (b : ResponseBuilder) :
    (errorStage.onResponse c b).build = applyPage (pathOf c) b.build := by
  show (b.mapResp (applyPage (pathOf c))).build = applyPage (pathOf c) b.build
  rw [build_mapResp]

/-- **The DEPLOYED braid stage's built effect (marker present).** When the
`x-error-page` marker is present, the built response of the deployed
`Reactor.Deploy.errorPageBraidStage.onResponse` (a stage of `braidedChain2`) is the
SAME `applyPage (pathOf c) b.build` — grounding the flat form in the actual
deployed pipeline stage, via the deploy-side `errorPageBraidStage_on`. -/
theorem errorBraid_resp_effect (c : Ctx) (b : ResponseBuilder) (nv : Bytes × Bytes)
    (hfind : c.req.headers.find? (fun nv => nv.1 == Reactor.Deploy.errorPageMarker) = some nv) :
    (Reactor.Deploy.errorPageBraidStage.onResponse c b).build = applyPage (pathOf c) b.build := by
  rw [Reactor.Deploy.errorPageBraidStage_on c b nv hfind, build_mapResp]

/-! ## 2. The flat body — XSS escape and page render, byte-grain -/

/-- **The flat HTML escape.** Escape the path bytes with a flat accumulator fold
(`foldAppend`, one flat `Array.++` per byte into the uniquely-owned accumulator, no
per-byte cons-spine) — the flat sibling of `htmlEscape`'s `flatMap`. -/
def flatHtmlEscape (bs : Bytes) : Array UInt8 :=
  foldAppend (fun b => (escByte b).toArray) #[] bs

/-- **The flat escape refines `htmlEscape` — byte-identical.** A direct instance of
the FOLD combinator `refine_fold`: the flat push-fold reads back exactly
`bs.flatMap escByte`. Non-vacuous — the flat op genuinely pushes each escaped byte;
the content is proven equal, not assumed. -/
theorem flatHtmlEscape_refines (bs : Bytes) :
    Datapath.Refinement.Refines (htmlEscape bs) (flatHtmlEscape bs) := by
  show (flatHtmlEscape bs).toList = htmlEscape bs
  unfold flatHtmlEscape htmlEscape
  rw [refine_fold (fun b => (escByte b).toArray) bs #[]]
  simp

/-- **The flat rendered page.** The template chunks with the flat escaped path
spliced in, joined by the flat `++` combinator (`Array.++`, the shared-operand
append). This is the flat sibling of `renderPage = tplPre ++ htmlEscape path ++ tplPost`. -/
def flatRenderPage (path : Bytes) : Array UInt8 :=
  tplPre.toArray ++ flatHtmlEscape path ++ tplPost.toArray

/-- **The flat rendered page refines `renderPage` — byte-identical.** Built by the
`++` combinator (`refine_append`, a `RefinesFn2`) over the template chunks with the
flat escaped path (`flatHtmlEscape_refines`) as the middle operand and the literal
template chunks as refined leaves (`refine_ofList`). No re-specification: the
deployed `renderPage` structure maps to the flat combinators and the byte equality
follows. -/
theorem flatRenderPage_refines (path : Bytes) :
    Datapath.Refinement.Refines (renderPage path) (flatRenderPage path) := by
  show (flatRenderPage path).toList = renderPage path
  simp only [flatRenderPage, renderPage, Array.toList_append, List.toList_toArray,
    show (flatHtmlEscape path).toList = htmlEscape path from flatHtmlEscape_refines path]

/-! ## 3. The flat whole-`Response` transform, EQUAL to the deployed `applyPage` -/

/-- **The flat error-page transform.** On a status with a configured page, replace
the body with the FLAT rendered page (`flatRenderPage`, materialized at the
`Response.body` `List` boundary — the named residual seam); otherwise the identity.
The flat sibling of the deployed `applyPage`. -/
def flatApplyPage (path : Bytes) (r : Response) : Response :=
  if hasPage r.status then { r with body := (flatRenderPage path).toList } else r

/-- **The flat transform EQUALS the deployed `applyPage`** — proven via the body
refinement `flatRenderPage_refines` (the byte equality transferred through the `if`),
not by definition. -/
theorem flatApplyPage_eq (path : Bytes) (r : Response) :
    flatApplyPage path r = applyPage path r := by
  unfold flatApplyPage applyPage
  rw [show (flatRenderPage path).toList = renderPage path from flatRenderPage_refines path]

/-- The flat transform IS the deployed stage's built response (on the request path),
grounding the flat form end-to-end in the real `errorStage`. -/
theorem flatApplyPage_eq_stage (c : Ctx) (b : ResponseBuilder) :
    flatApplyPage (pathOf c) b.build = (errorStage.onResponse c b).build := by
  rw [errorStage_resp_effect, flatApplyPage_eq]

/-! ## 4. Full serialize: the flat stage's whole response is byte-identical -/

/-- **THE FULL BYTE-IDENTITY.** The flat error-page stage's whole serialized
response (flat body build ⟶ `Datapath.ByteRefine.flatSerialize`, the derived flat
serializer) is byte-identical to `Reactor.serialize` of the DEPLOYED stage's
response. Chains the body equality (`flatApplyPage_eq`) into the byte-grain
serialize equality (`flatSerialize_refines`). No deployed byte changes; the whole
computation is flat but for the one named `.toList` body seam. -/
theorem flatError_serialize_refines (path : Bytes) (r : Response) :
    Datapath.Refinement.Refines (Reactor.serialize (applyPage path r))
      (flatSerialize (flatApplyPage path r)) := by
  rw [flatApplyPage_eq]
  exact flatSerialize_refines (applyPage path r)

/-! ## Non-vacuity — the flat ops genuinely compute the REAL deployed effect -/

-- The flat rendered page over the real request path equals the deployed
-- `renderPage` — evaluated by the kernel (not just proven).
#guard (flatRenderPage (pathOf missingCtx)).toList == renderPage (pathOf missingCtx)

-- The flat escape genuinely neutralizes XSS: `/<s>` escapes its angle brackets,
-- byte-identical to the library's `renderPage_xss_safe` witness.
#guard (flatHtmlEscape [47, 60, 115, 62]).toList == [47, 38, 108, 116, 59, 115, 38, 103, 116, 59]

-- The flat transform genuinely rewrites the deployed 404 body to the custom page
-- (the REAL deployed stage effect: `applyPage` on a configured status).
#guard (flatApplyPage (pathOf missingCtx) default404).body == renderPage (pathOf missingCtx)

-- The bytes really change — the flat op is not a constant/identity on a 404.
#guard (flatApplyPage (pathOf missingCtx) default404).body != default404.body

-- The status is untouched (a matched 404 stays a 404).
#guard (flatApplyPage (pathOf missingCtx) default404).status == 404

-- On a status with no configured page (200), the flat transform passes the body
-- through untouched (the gate genuinely branches — no custom page written).
#guard (flatApplyPage (pathOf missingCtx) (Reactor.ok200 "hi".toUTF8.toList)).body
        == (Reactor.ok200 "hi".toUTF8.toList).body
#guard (flatApplyPage (pathOf missingCtx) (Reactor.ok200 "hi".toUTF8.toList)).body
        != renderPage (pathOf missingCtx)

-- The flat op genuinely depends on the input path: different paths ⇒ different
-- flat rendered bytes (not a constant).
#guard (flatRenderPage [47]).toList != (flatRenderPage [47, 120]).toList

-- THE FULL flat serialized response is byte-identical to the deployed serialize —
-- evaluated on the real 404 → custom-page rewrite.
#guard (flatSerialize (flatApplyPage (pathOf missingCtx) default404)).data.toList
        == Reactor.serialize (applyPage (pathOf missingCtx) default404)

/-! ## Axiom audit (fully-qualified) -/

#print axioms Datapath.FlatStageErrpage.errorStage_resp_effect
#print axioms Datapath.FlatStageErrpage.errorBraid_resp_effect
#print axioms Datapath.FlatStageErrpage.flatHtmlEscape_refines
#print axioms Datapath.FlatStageErrpage.flatRenderPage_refines
#print axioms Datapath.FlatStageErrpage.flatApplyPage_eq
#print axioms Datapath.FlatStageErrpage.flatApplyPage_eq_stage
#print axioms Datapath.FlatStageErrpage.flatError_serialize_refines

end Datapath.FlatStageErrpage
