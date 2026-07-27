import Datapath.FlatHeaders
import Reactor.Stage.SecurityHeaders

/-!
# Datapath.FlatStage — ONE representative stage proven flat, byte-identical to its
deployed `List` form, and the composition skeleton for the remaining stages.

The representative stage is `securityheaders`
(`Reactor.Stage.SecurityHeaders.securityheadersStage`, position 13 of the 14 in
`Reactor.Deploy.deployStagesFull2`): a closed, data-independent header-transform
whose whole response-phase effect is folding a fixed header set
(`wireHeaders policy`) onto the response header block. It is the simplest genuine
header-transform stage, so it de-risks the pattern for the other header stages
(`cors`, `headerRewrite`, the deploy `header` stage) and the gate stages.

## What is proven here (equality-transfer, NOT a re-spec)

* `securityStage_headers_effect` — the *deployed* stage's net effect on the built
  response header block is exactly `hs ++ wireHeaders policy`, read off the real
  `securityheadersStage.onResponse` via `Reactor.Pipeline.build_addHeaders`. This
  grounds the flat form in the ACTUAL deployed function; we do not re-specify the
  stage.
* `flatSecurityStage` + `flatSecurityStage_refines` — the flat form runs on the
  flat `HdrBlock` (`Array.push` fold, no per-stage spine copy) and is proven to
  compute the SAME header effect (`RefinesHdrFn (· ++ wireHeaders policy)`), via
  the header FOLD combinator `HdrBlock.denote_foldAddHeader`. Non-vacuous: the flat
  fold genuinely pushes; the refinement is the push-fold = append-fold equality.
* `flatSecurityStage_render_byte_identical` — composing the header-grain stage
  refinement with the byte-grain flat renderer (`RefinesHdrFn.compRender`) proves
  the flat stage's rendered header bytes are byte-identical to
  `Reactor.renderHeaders` of the deployed stage's header block.
* `flatSecurity_serialize_refines` — the full serialized response of the flat
  stage is byte-identical to `Reactor.serialize` of the deployed stage's response,
  chaining the header-block refinement into the derived flat serializer
  `Datapath.ByteRefine.flatSerialize` (whose `flatSerialize_refines` is the
  byte-grain serialize equality).
* `frameTail_comp` — a concrete use of the EXISTING byte-grain functor law
  `Datapath.Refinement.RefinesFn.comp`, chaining the flat rendered header bytes
  through the serialize frame tail (`++ CRLF CRLF ++ body`, as shared right
  operands) — the pattern the remaining byte-grain seams reuse.

## The composition skeleton for the remaining 13 stages

`RefinesHdrFn.comp` (the header-grain functor law) composes header-transform
stages for free: a pipeline `gc ∘ fc` of refined header stages refines
`ga ∘ fa`. `twoHeaderStages_comp` demonstrates it on `securityheaders` followed by
a second header append. So the remaining header-transform stages are the SAME
mechanical recipe — express each stage's `List`-header effect as a fixed fold and
discharge by `refinesHdr_foldAddHeader`; the gate stages (`ipfilter`, `redirect`,
…) are simpler still (a decision on the request, no header fold). What genuinely
remains is named at the bottom (`REMAINING`).
-/

namespace Datapath.FlatStage

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx ResponseBuilder build_addHeaders runPipeline)
open Reactor.Stage.SecurityHeaders (securityheadersStage wireHeaders policy)
open Datapath.FlatHeaders
open Datapath.Refinement

/-! ## 1. The deployed stage's header effect, read off the REAL stage -/

/-- **The deployed `securityheaders` stage's net header effect — grounded, not
re-specified.** For any context and any incoming builder, the BUILT response of
the real `securityheadersStage.onResponse` has header block `b.build.headers ++
wireHeaders policy`. Proven directly from the stage's definition (its `onResponse`
folds `ResponseBuilder.addHeader` over `wireHeaders policy`) and the deployed
faithfulness lemma `Reactor.Pipeline.build_addHeaders`. This is the function the
flat form must compute. -/
theorem securityStage_headers_effect (c : Ctx) (b : ResponseBuilder) :
    ((securityheadersStage.onResponse c b).build).headers
      = b.build.headers ++ wireHeaders policy := by
  show (((wireHeaders policy).foldl ResponseBuilder.addHeader b).build).headers
      = b.build.headers ++ wireHeaders policy
  rw [build_addHeaders]

/-! ## 2. The flat stage and its refinement (header grain) -/

/-- **The flat `securityheaders` stage.** Runs on the flat `HdrBlock`: fold the
fixed security-header set onto the flat block via `Array.push` (amortized `O(1)`
per header, no per-stage header-spine copy). This is the flat sibling of the
deployed stage's `(wireHeaders policy).foldl ResponseBuilder.addHeader`. -/
def flatSecurityStage (h : HdrBlock) : HdrBlock :=
  (wireHeaders policy).foldl HdrBlock.addHeader h

/-- **The flat stage refines the deployed stage's header effect.** `flatSecurityStage`
computes `· ++ wireHeaders policy` on the denotation — the exact function
`securityStage_headers_effect` reads off the deployed stage. A direct instance of
the header FOLD combinator `refinesHdr_foldAddHeader` (⇐ `HdrBlock.denote_foldAddHeader`).
Non-vacuous: the flat op folds `Array.push`; the content is proven equal, not
assumed. -/
theorem flatSecurityStage_refines :
    RefinesHdrFn (fun hs => hs ++ wireHeaders policy) flatSecurityStage :=
  refinesHdr_foldAddHeader (wireHeaders policy)

/-! ## 3. Byte-identical: the flat stage rendered = the deployed stage rendered -/

/-- **The flat stage's rendered header bytes are byte-identical to the deployed
stage's.** Given any flat block refining the abstract header list `a`, the flat
stage's output rendered through the flat renderer equals
`Reactor.renderHeaders (a ++ wireHeaders policy)` — `renderHeaders` of exactly the
header block `securityStage_headers_effect` produces. This is
`RefinesHdrFn.compRender`: the header-grain stage refinement composed with the
byte-grain flat renderer, across the grain boundary, in one step. The header block
is rendered flat with NO materialization back to a `List` (the seam
`flatSecurity_serialize_refines` still pays; see REMAINING). -/
theorem flatSecurityStage_render_byte_identical
    {a : List (Bytes × Bytes)} {h : HdrBlock} (r : RefinesHdr a h) :
    Datapath.Refinement.Refines (Reactor.renderHeaders (a ++ wireHeaders policy))
      (flatRenderBlock (flatSecurityStage h)) :=
  flatSecurityStage_refines.compRender r

/-- Specialized to the deployed stage: the flat rendering of the flat security
stage over a base header list `hs` is byte-identical to `renderHeaders` of the
header block the deployed stage builds on `hs` (`securityStage_headers_effect`
with `b.build.headers = hs`). -/
theorem flatSecurityStage_render_matches_deployed (hs : List (Bytes × Bytes)) :
    Datapath.Refinement.Refines (Reactor.renderHeaders (hs ++ wireHeaders policy))
      (flatRenderBlock (flatSecurityStage (HdrBlock.ofList hs))) :=
  flatSecurityStage_render_byte_identical (h := HdrBlock.ofList hs)
    (by simp [RefinesHdr])

/-! ## 4. Full serialize: the flat stage's whole response is byte-identical -/

/-- The response the DEPLOYED security stage yields from a base response `r` — its
header block extended by `wireHeaders policy` (`securityStage_headers_effect`;
`securedResp_eq_stage` ties it to the real `onResponse`). -/
def securedResp (r : Response) : Response :=
  { r with headers := r.headers ++ wireHeaders policy }

/-- `securedResp` IS the deployed stage's built response — grounding the flat
end-to-end theorem in the actual stage. -/
theorem securedResp_eq_stage (c : Ctx) (b : ResponseBuilder) :
    (securityheadersStage.onResponse c b).build = securedResp b.build := by
  show ((wireHeaders policy).foldl ResponseBuilder.addHeader b).build
      = { b.build with headers := b.build.headers ++ wireHeaders policy }
  rw [build_addHeaders]

/-- The flat computation of the security-stage response: accumulate the header
block flat with `flatSecurityStage` (`Array.push` fold), then present it for
serialization. The single `denote` (Array → List) at the `Response.headers`
boundary is the named residual seam (REMAINING (b)); the header accumulation and
the serialization are both flat. -/
def flatSecuredResp (r : Response) : Response :=
  { r with headers := (flatSecurityStage (HdrBlock.ofList r.headers)).denote }

/-- The flat security response equals the deployed one — PROVEN via the push-fold =
append-fold refinement, not by definition. -/
theorem flatSecuredResp_eq (r : Response) : flatSecuredResp r = securedResp r := by
  have hh : (flatSecurityStage (HdrBlock.ofList r.headers)).denote
      = r.headers ++ wireHeaders policy := by
    rw [flatSecurityStage_refines (HdrBlock.ofList r.headers), HdrBlock.denote_ofList]
  show { r with headers := (flatSecurityStage (HdrBlock.ofList r.headers)).denote }
      = { r with headers := r.headers ++ wireHeaders policy }
  rw [hh]

/-- **THE FULL BYTE-IDENTITY.** The flat security stage's whole serialized response
(flat header accumulation ⟶ `Datapath.ByteRefine.flatSerialize`, the derived flat
serializer) is byte-identical to `Reactor.serialize` of the DEPLOYED stage's
response. Chains the header-block refinement (`flatSecuredResp_eq`) into the
byte-grain serialize equality (`flatSerialize_refines`). No deployed byte changes;
the whole computation is flat but for the one named `denote` seam. -/
theorem flatSecurity_serialize_refines (r : Response) :
    Datapath.Refinement.Refines (Reactor.serialize (securedResp r)) (flatSerialize (flatSecuredResp r)) := by
  rw [flatSecuredResp_eq]
  exact flatSerialize_refines (securedResp r)

/-! ## 5. The composition skeleton — how the remaining stages chain (functor laws) -/

/-- **The header-grain functor law, demonstrated.** Two header-transform stages
compose by `RefinesHdrFn.comp` with NO extra per-stage work: `securityheaders`
followed by a second fixed header append refines the composed `List` header
pipeline `(· ++ [nv]) ∘ (· ++ wireHeaders policy)`. This is the skeleton the other
header-transform stages (`cors`, `headerRewrite`, the deploy `header` stage) drop
into — each is a `refinesHdr_foldAddHeader` instance, and `comp` chains them for
free. -/
theorem twoHeaderStages_comp (nv : Bytes × Bytes) :
    RefinesHdrFn ((fun hs => hs ++ [nv]) ∘ (fun hs => hs ++ wireHeaders policy))
      ((fun h => h.addHeader nv) ∘ flatSecurityStage) :=
  (flatSecurityStage_refines).comp (refinesHdr_addHeader nv)

/-- **A concrete use of the EXISTING byte-grain functor law
`Datapath.Refinement.RefinesFn.comp`.** After the header block renders flat, the
serialize frame tail — append the blank-line separator (`CRLF CRLF`) then the body
— is two byte-grain refined combinators (`refine_append_shared`, i.e.
`RefinesFn2.right`) composed by `RefinesFn.comp`, applied to the flat rendered
header bytes. So the flat rendered security-stage headers, followed by the frame
tail, is byte-identical to `renderHeaders (hs ++ wireHeaders policy) ++ CRLF CRLF ++ body`.
This is the byte-grain half of the serialize chain, the pattern the serializer
seam reuses. -/
theorem frameTail_comp (hs : List (Bytes × Bytes)) (body : Bytes) :
    Datapath.Refinement.Refines
      (Reactor.renderHeaders (hs ++ wireHeaders policy)
        ++ (Reactor.crlf ++ Reactor.crlf) ++ body)
      ((flatRenderBlock (flatSecurityStage (HdrBlock.ofList hs))
        ++ (Reactor.crlf ++ Reactor.crlf).toArray) ++ body.toArray) := by
  -- the two byte-grain frame-tail appends, composed by the EXISTING functor law
  have hsep : Datapath.Refinement.Refines (Reactor.crlf ++ Reactor.crlf)
      (Reactor.crlf ++ Reactor.crlf).toArray := refine_ofList _
  have hbody : Datapath.Refinement.Refines body body.toArray := refine_ofList _
  have hchain :
      RefinesFn ((fun x => x ++ body) ∘ (fun x => x ++ (Reactor.crlf ++ Reactor.crlf)))
        ((fun x : Array UInt8 => x ++ body.toArray) ∘
          (fun x : Array UInt8 => x ++ (Reactor.crlf ++ Reactor.crlf).toArray)) :=
    (refine_append_shared hsep).comp (refine_append_shared hbody)
  have happ := hchain.apply (flatSecurityStage_render_matches_deployed hs)
  simpa [Function.comp, List.append_assoc, Array.append_assoc] using happ

/-! ## Non-vacuity — the flat ops genuinely compute, witnessed on real inputs -/

-- The flat security stage over a real base header list produces the deployed
-- header block, evaluated by the kernel (not just proven).
#guard (flatSecurityStage (HdrBlock.ofList [("X-Test".toUTF8.toList, "1".toUTF8.toList)])).denote
        == [("X-Test".toUTF8.toList, "1".toUTF8.toList)] ++ wireHeaders policy

-- The flat rendered header bytes of the flat stage equal `renderHeaders` of the
-- deployed header block — evaluated.
#guard (flatRenderBlock (flatSecurityStage (HdrBlock.ofList [("X-Test".toUTF8.toList, "1".toUTF8.toList)]))).toList
        == Reactor.renderHeaders ([("X-Test".toUTF8.toList, "1".toUTF8.toList)] ++ wireHeaders policy)

-- The flat op genuinely depends on the input: different base headers give
-- different flat rendered bytes (not a constant).
#guard (flatRenderBlock (flatSecurityStage (HdrBlock.ofList [("A".toUTF8.toList, "1".toUTF8.toList)]))).toList
        != (flatRenderBlock (flatSecurityStage (HdrBlock.ofList [("B".toUTF8.toList, "22".toUTF8.toList)]))).toList

-- The full flat serialized response is byte-identical to the deployed serialize —
-- evaluated on a real `200 OK`.
#guard (flatSerialize (flatSecuredResp (Reactor.ok200 "hi".toUTF8.toList))).data.toList
        == Reactor.serialize (securedResp (Reactor.ok200 "hi".toUTF8.toList))

/-! ## REMAINING (the honest residual for the whole cons-list removal)

This slice de-risked ONE stage end-to-end. What remains, named precisely:

* **(a) The other 13 stages of `deployStagesFull2`.** The header-transform stages
  (`cors`, `headerRewrite`, the deploy `header` stage) are the SAME recipe:
  express the stage's `List`-header effect as a fixed fold and discharge by
  `refinesHdr_foldAddHeader`; `RefinesHdrFn.comp` chains them (`twoHeaderStages_comp`).
  A stage whose effect is a whole-`Response` `mapResp` (not a pure header append)
  needs its transform expressed on `HdrBlock` — mechanical but per-stage. The gate
  stages (`jwt`, `basicauth`, `ipfilter`, `rate`, `cache`, `redirect`, `traversal`,
  `policy`, `gzip`, `htmlrewrite`) decide on the REQUEST; their response phase is
  transparent or a fixed header set — simpler than this stage. `gzip`/`htmlrewrite`
  transform the BODY, which is `Datapath.ByteRefine`'s byte grain, already covered
  by `refine_map`/`refine_fold`.

* **(b) The `Response.headers` `List` seam.** `flatSecuredResp` still `denote`s the
  flat `HdrBlock` back to a `List` at the `Reactor.Response.headers` field boundary
  (the deployed `Response` is `List`-typed). `flatSecurityStage_render_byte_identical`
  shows the header block renders flat with NO such materialization; closing (b)
  fully is a flat `Wire`/`serialize` variant taking `HdrBlock` directly (additive,
  ~1 file), so the whole serialize never touches a header cons-cell.

* **(c) The request-read + write codegen seams.** Unchanged from
  `Datapath.Serve`/`Datapath.Span`: `s.read`/`writeResp` are the named codegen
  obligations (`leanc` will not fuse `List UInt8` on its own). This slice is the
  response header-block half; the request/parse half is `spanParseRequest_refines`
  + the `read` seam; the write half is `writeInPlace` + `OutFitsResponse`.

**Re-estimate.** This stage: ~80 model LOC + ~110 header-rep LOC (`FlatHeaders`,
reused by every header stage). The header-rep is a fixed cost paid once. Each
remaining header-transform stage ≈ this stage minus the rep ≈ 40–70 LOC; each gate
stage ≈ 20–40 LOC. 13 stages ⇒ ~0.5–0.8k LOC — consistent with the scope's
+600–1,000 Lean-LOC estimate for step 1, BOUNDED confirmed. The codegen seam (c)
is unchanged (the one genuinely-open piece).
-/

end Datapath.FlatStage
