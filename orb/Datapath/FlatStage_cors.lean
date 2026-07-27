import Datapath.FlatHeaders
import Reactor.Stage.Cors

/-!
# Datapath.FlatStage_cors — the deployed `cors` stage proven flat, byte-identical
to its `List` form.

The `cors` stage (`Reactor.Stage.Cors.corsStage`, one of the header-transform
stages of the deployed serve) is a *context-conditional* header append: on the
response phase it stamps `Access-Control-Allow-Origin: <value>` onto the affine
`ResponseBuilder` **iff** the request's `Origin` is admitted by the deployed
policy (`Cors.acaoValue corsPolicy (originOf c)`), and adds nothing otherwise.

Unlike `securityheaders` (a fixed header set, no request dependence), the cors
effect is parameterized by the context `c`. But at any fixed `c` it is STILL a
plain header append of a fixed list — `corsHeaders c`, the singleton
`[(ACAO, value)]` when the origin is allowed and `[]` when it is denied. That is
exactly the shape `Datapath.FlatHeaders`' header-grain calculus refines, so the
same header-transform recipe applies, one `refinesHdr_foldAddHeader` instance per
context.

## What is proven here (equality-transfer, NOT a re-spec)

* `corsStage_headers_effect` — the *deployed* stage's net effect on the built
  response header block is exactly `hs ++ corsHeaders c`, read off the real
  `corsStage.onResponse` (its allow/deny branch) via `build_addHeader`. This
  grounds the flat form in the ACTUAL deployed function; the effect is not
  re-specified — `corsHeaders c` is read out of the stage's own match.
* `flatCorsStage` + `flatCorsStage_refines` — the flat form folds `corsHeaders c`
  onto the flat `HdrBlock` by `Array.push` and is proven to compute the SAME
  header effect (`RefinesHdrFn (· ++ corsHeaders c)`), via
  `refinesHdr_foldAddHeader`. Non-vacuous: the fold genuinely pushes (a real ACAO
  header for an allowed origin, nothing for a denied one); the content is proven
  equal, not assumed.
* `flatCorsStage_render_byte_identical` — the header-grain stage refinement
  composed with the byte-grain flat renderer (`RefinesHdrFn.compRender`): the flat
  stage's rendered header bytes are byte-identical to `Reactor.renderHeaders` of
  the deployed stage's header block.
* `flatCors_serialize_refines` — the full serialized response of the flat stage is
  byte-identical to `Reactor.serialize` of the deployed stage's response, chaining
  the header-block refinement into the derived flat serializer
  `Datapath.ByteRefine.flatSerialize`.

This mirrors `Datapath.FlatStage` (the `securityheaders` exemplar) exactly, one
extra `cases` on the allow/deny branch being the only difference.
-/

namespace Datapath.FlatStage_cors

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx ResponseBuilder build_addHeader)
open Reactor.Stage.Cors
  (corsStage corsPolicy originOf acaoName strBytes allowedCtx originHeaderName)
open Datapath.FlatHeaders
open Datapath.Refinement

/-! ## 1. The deployed stage's header effect, read off the REAL stage -/

/-- **The list the deployed `cors` stage appends at context `c` — read off the
stage, not re-specified.** Exactly the `corsStage.onResponse` allow/deny branch:
the singleton `Access-Control-Allow-Origin` pair when `Cors.acaoValue` admits the
origin, and the empty list when it does not. -/
def corsHeaders (c : Ctx) : List (Bytes × Bytes) :=
  match Cors.acaoValue corsPolicy (originOf c) with
  | some v => [(acaoName, strBytes v)]
  | none   => []

/-- **The deployed `cors` stage's net header effect — grounded, not re-specified.**
For any context and any incoming builder, the BUILT response of the real
`corsStage.onResponse` has header block `b.build.headers ++ corsHeaders c`. Proven
directly from the stage's definition (its allow/deny `match`) and the deployed
faithfulness lemma `Reactor.Pipeline.build_addHeader`. This is the function the
flat form must compute. -/
theorem corsStage_headers_effect (c : Ctx) (b : ResponseBuilder) :
    ((corsStage.onResponse c b).build).headers
      = b.build.headers ++ corsHeaders c := by
  show ((match Cors.acaoValue corsPolicy (originOf c) with
          | some v => b.addHeader (acaoName, strBytes v)
          | none   => b).build).headers
      = b.build.headers ++ corsHeaders c
  unfold corsHeaders
  cases Cors.acaoValue corsPolicy (originOf c) with
  | some v => simp [build_addHeader]
  | none   => simp

/-! ## 2. The flat stage and its refinement (header grain) -/

/-- **The flat `cors` stage.** Runs on the flat `HdrBlock`: fold the
context-conditional header list `corsHeaders c` onto the flat block via
`Array.push` (amortized `O(1)`, no per-stage header-spine copy). The flat sibling
of the deployed stage's allow/deny append. -/
def flatCorsStage (c : Ctx) (h : HdrBlock) : HdrBlock :=
  (corsHeaders c).foldl HdrBlock.addHeader h

/-- **The flat stage refines the deployed stage's header effect.** `flatCorsStage c`
computes `· ++ corsHeaders c` on the denotation — the exact function
`corsStage_headers_effect` reads off the deployed stage. A direct instance of the
header FOLD combinator `refinesHdr_foldAddHeader`. Non-vacuous: the flat op folds
`Array.push`; the content is proven equal, not assumed. -/
theorem flatCorsStage_refines (c : Ctx) :
    RefinesHdrFn (fun hs => hs ++ corsHeaders c) (flatCorsStage c) :=
  refinesHdr_foldAddHeader (corsHeaders c)

/-! ## 3. Byte-identical: the flat stage rendered = the deployed stage rendered -/

/-- **The flat stage's rendered header bytes are byte-identical to the deployed
stage's.** Given any flat block refining the abstract header list `a`, the flat
stage's output rendered through the flat renderer equals
`Reactor.renderHeaders (a ++ corsHeaders c)` — `renderHeaders` of exactly the
header block `corsStage_headers_effect` produces. This is
`RefinesHdrFn.compRender`: the header-grain stage refinement composed with the
byte-grain flat renderer, across the grain boundary, in one step. -/
theorem flatCorsStage_render_byte_identical (c : Ctx)
    {a : List (Bytes × Bytes)} {h : HdrBlock} (r : RefinesHdr a h) :
    Datapath.Refinement.Refines (Reactor.renderHeaders (a ++ corsHeaders c))
      (flatRenderBlock (flatCorsStage c h)) :=
  (flatCorsStage_refines c).compRender r

/-- Specialized to the deployed stage: the flat rendering of the flat cors stage
over a base header list `hs` is byte-identical to `renderHeaders` of the header
block the deployed stage builds on `hs` (`corsStage_headers_effect` with
`b.build.headers = hs`). -/
theorem flatCorsStage_render_matches_deployed (c : Ctx) (hs : List (Bytes × Bytes)) :
    Datapath.Refinement.Refines (Reactor.renderHeaders (hs ++ corsHeaders c))
      (flatRenderBlock (flatCorsStage c (HdrBlock.ofList hs))) :=
  flatCorsStage_render_byte_identical c (h := HdrBlock.ofList hs)
    (by simp [RefinesHdr])

/-! ## 4. Full serialize: the flat stage's whole response is byte-identical -/

/-- The response the DEPLOYED cors stage yields from a base response `r` — its
header block extended by `corsHeaders c` (`corsStage_headers_effect`;
`corsResp_eq_stage` ties it to the real `onResponse`). -/
def corsResp (c : Ctx) (r : Response) : Response :=
  { r with headers := r.headers ++ corsHeaders c }

/-- `corsResp` IS the deployed stage's built response — grounding the flat
end-to-end theorem in the actual stage. -/
theorem corsResp_eq_stage (c : Ctx) (b : ResponseBuilder) :
    (corsStage.onResponse c b).build = corsResp c b.build := by
  show (match Cors.acaoValue corsPolicy (originOf c) with
          | some v => b.addHeader (acaoName, strBytes v)
          | none   => b).build
      = corsResp c b.build
  unfold corsResp corsHeaders
  cases Cors.acaoValue corsPolicy (originOf c) with
  | some v => rw [build_addHeader]
  | none   => simp

/-- The flat computation of the cors-stage response: accumulate the header block
flat with `flatCorsStage` (`Array.push` fold), then present it for serialization.
The single `denote` (Array → List) at the `Response.headers` boundary is the named
residual seam (shared with `Datapath.FlatStage`); the header accumulation and the
serialization are both flat. -/
def flatCorsResp (c : Ctx) (r : Response) : Response :=
  { r with headers := (flatCorsStage c (HdrBlock.ofList r.headers)).denote }

/-- The flat cors response equals the deployed one — PROVEN via the push-fold =
append-fold refinement, not by definition. -/
theorem flatCorsResp_eq (c : Ctx) (r : Response) : flatCorsResp c r = corsResp c r := by
  have hh : (flatCorsStage c (HdrBlock.ofList r.headers)).denote
      = r.headers ++ corsHeaders c := by
    rw [flatCorsStage_refines c (HdrBlock.ofList r.headers), HdrBlock.denote_ofList]
  show { r with headers := (flatCorsStage c (HdrBlock.ofList r.headers)).denote }
      = { r with headers := r.headers ++ corsHeaders c }
  rw [hh]

/-- **THE FULL BYTE-IDENTITY.** The flat cors stage's whole serialized response
(flat header accumulation ⟶ `Datapath.ByteRefine.flatSerialize`, the derived flat
serializer) is byte-identical to `Reactor.serialize` of the DEPLOYED stage's
response. Chains the header-block refinement (`flatCorsResp_eq`) into the
byte-grain serialize equality (`flatSerialize_refines`). No deployed byte changes;
the whole computation is flat but for the one named `denote` seam. -/
theorem flatCors_serialize_refines (c : Ctx) (r : Response) :
    Datapath.Refinement.Refines (Reactor.serialize (corsResp c r)) (flatSerialize (flatCorsResp c r)) := by
  rw [flatCorsResp_eq]
  exact flatSerialize_refines (corsResp c r)

/-! ## Non-vacuity — the flat op genuinely computes the REAL deployed effect -/

-- The flat cors stage's effect list at the ALLOWED context is the REAL
-- `Access-Control-Allow-Origin` header the deployed policy grants — evaluated by
-- the kernel, not just proven. This is the actual deployed stage effect.
#guard corsHeaders allowedCtx == [(acaoName, strBytes "https://app.example.com")]

-- A context with no `Origin` header is denied: the flat effect is empty (the
-- no-leak boundary), so the stage adds nothing — evaluated.
#guard corsHeaders { input := [], req := { headers := [] } } == ([] : List (Bytes × Bytes))

-- The flat cors stage over a real base header list, at the allowed context,
-- produces the deployed header block (base ++ ACAO) — evaluated.
#guard (flatCorsStage allowedCtx (HdrBlock.ofList [("X-Test".toUTF8.toList, "1".toUTF8.toList)])).denote
        == [("X-Test".toUTF8.toList, "1".toUTF8.toList)] ++ corsHeaders allowedCtx

-- The flat rendered header bytes of the flat stage equal `renderHeaders` of the
-- deployed header block — evaluated.
#guard (flatRenderBlock (flatCorsStage allowedCtx (HdrBlock.ofList [("X-Test".toUTF8.toList, "1".toUTF8.toList)]))).toList
        == Reactor.renderHeaders ([("X-Test".toUTF8.toList, "1".toUTF8.toList)] ++ corsHeaders allowedCtx)

-- The flat op genuinely depends on the CORS decision: an allowed origin renders
-- different bytes than a denied one (ACAO present vs absent) — not a constant.
#guard (flatRenderBlock (flatCorsStage allowedCtx (HdrBlock.ofList []))).toList
        != (flatRenderBlock (flatCorsStage { input := [], req := { headers := [] } } (HdrBlock.ofList []))).toList

-- The full flat serialized response is byte-identical to the deployed serialize —
-- evaluated on a real `200 OK` at the allowed context.
#guard (flatSerialize (flatCorsResp allowedCtx (Reactor.ok200 "hi".toUTF8.toList))).data.toList
        == Reactor.serialize (corsResp allowedCtx (Reactor.ok200 "hi".toUTF8.toList))

end Datapath.FlatStage_cors
