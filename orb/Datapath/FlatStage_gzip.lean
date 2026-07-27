import Datapath.FlatHeaders
import Reactor.Stage.Gzip

/-!
# Datapath.FlatStage_gzip — the deployed `gzip` stage (position 10 of
`Reactor.Deploy.deployStagesFull2`) proven flat, byte-identical to its deployed
`List` form, via the BODY path of the refinement calculus.

Unlike the header-transform stage `securityheaders` (`Datapath.FlatStage`), the
deployed `gzip` stage's whole-response effect is a BODY rewrite plus one header
push:

* the BODY becomes `Gzip.gzipStored r.body` — the real RFC 1952 container
  (`mkHeader ‖ deflateStored r.body ‖ CRC-32 ‖ ISIZE`), read off the deployed
  `Reactor.Stage.Gzip.gzipBody` / `gzipStage.onResponse`;
* the HEADER block gains `Content-Encoding: gzip`
  (`Reactor.Stage.Gzip.ceName`, `gzipVal`).

So this stage exercises the BODY grain of `Datapath.ByteRefine` (the `Array UInt8`
FOLD combinator) for the body, and the header grain (`HdrBlock` push-fold) for the
`Content-Encoding` header — the two halves the scope named.

## The body transform IS a `refine_fold` — grounded, not re-specified

`Gzip.gzipStored x` is definitionally the left-associated `List.++` chain
`mkHeader ++ deflateStored x ++ u32le (crc32 x).toNat ++ u32le (x.length % 2³²)`.
`gzipStored_eq_flatten` re-presents that chain as the `flatten` of a FIXED fragment
list `gzipFragments x` (`renderHeaders_eq_flatten`'s sibling on the body). The flat
body transform is then `foldAppend List.toArray #[] (gzipFragments x)` — the byte
FOLD combinator applied to those fragments — and `flatGzipBody_refines` proves it
computes byte-identical bytes to `Gzip.gzipStored x` **for free** from
`foldAppend_toArray_refines` (the calculus's `refine_fold`). No new byte reasoning;
the container assembly's `++`-chain is discharged by the shared fold lemma.

## What is proven here (equality-transfer, BYTE-IDENTICAL, non-vacuous)

* `gzippedResp_eq_stage` — the DEPLOYED stage's built response on a gzip-accepting
  request is exactly `gzippedResp` (body ⟶ `Gzip.gzipStored`, headers ⟶
  `++ [(ceName, gzipVal)]`), read off `gzipStage.onResponse` via the deployed
  faithfulness lemmas `build_addHeader`/`build_mapResp`. Grounds the flat form in
  the ACTUAL deployed function; we do NOT re-specify the stage.
* `gzipStored_eq_flatten` — `Gzip.gzipStored` is the `flatten` of `gzipFragments`
  (the body's framing decomposition, read off `gzipStored`'s definition).
* `flatGzipBody` + `flatGzipBody_refines` — the flat body transform (the byte FOLD)
  computes byte-identical bytes to `Gzip.gzipStored`. Non-vacuous: it folds real
  `Array.++`s over the real container fragments; the bytes are proven equal.
* `flatGzippedResp` + `flatGzippedResp_eq` — the flat whole-response transform
  (flat body FOLD + flat header push) equals the deployed built response
  `gzippedResp` — PROVEN, both halves via their refinements.
* `flatGzip_serialize_refines` — the flat gzip stage's whole serialized response is
  byte-identical to `Reactor.serialize` of the DEPLOYED stage's response, chaining
  `flatGzippedResp_eq` into `flatSerialize_refines` (the byte-grain serialize
  equality). The whole computation is flat but for the named `List` seams.

## The honest residual (`RESIDUAL`, at the bottom)

The CONTAINER ASSEMBLY (`mkHeader ‖ deflate ‖ CRC ‖ size` concatenation) is proven
flat and byte-identical here. The FRAGMENT CONTENTS — `Gzip.deflateStored x` (the
DEFLATE block) and `Gzip.crc32 x` (the reflected-poly CRC fold) — remain `List`
computations producing the fragment bytes. gzip's entropy/DEFLATE coding and the
CRC fold are genuine loops (the `refine_fold` residual, consistent with
`Reactor.Stage.CompressBody`'s named entropy follow-on); they are NOT faked here.
-/

namespace Datapath.FlatStage_gzip

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx ResponseBuilder build_addHeader build_mapResp)
open Reactor.Stage.Gzip (gzipStage gzipBody ceName gzipVal acceptsGzip)
open Datapath.FlatHeaders
open Datapath.Refinement

/-! ## 1. The deployed stage's whole-response effect, read off the REAL stage -/

/-- **The deployed `gzip` stage's built response — grounded, not re-specified.** On
a gzip-accepting request, the finalized (`build`) response of the real
`gzipStage.onResponse` rewrites the body to the RFC 1952 container
`Gzip.gzipStored r.body` and appends `(ceName, gzipVal)` to the header block. This
is the function the flat form must compute. -/
def gzippedResp (r : Response) : Response :=
  { r with body := _root_.Gzip.gzipStored r.body
         , headers := r.headers ++ [(ceName, gzipVal)] }

/-- `gzippedResp` IS the deployed stage's built response on a gzip-accepting
request — grounding the flat end-to-end theorem in the actual `onResponse`. Read
directly off the stage's `mapResp gzipBody` (the body rewrite) and `addHeader`
(the header push) via `build_mapResp`/`build_addHeader`. -/
theorem gzippedResp_eq_stage (c : Ctx) (b : ResponseBuilder)
    (h : acceptsGzip c.req = true) :
    (gzipStage.onResponse c b).build = gzippedResp b.build := by
  show (match acceptsGzip c.req with
        | true  => (b.mapResp gzipBody).addHeader (ceName, gzipVal)
        | false => b).build = gzippedResp b.build
  rw [h, build_addHeader, build_mapResp]
  rfl

/-! ## 2. The body transform IS a `refine_fold` (byte grain) -/

/-- The gzip container as a FIXED list of byte fragments: the header, the DEFLATE
stored block, the CRC-32 trailer, the ISIZE trailer — mirroring `Gzip.gzipStored`'s
`++`-chain structure. `gzipStored_eq_flatten` proves its `flatten` is exactly
`gzipStored`. -/
def gzipFragments (x : Bytes) : List Bytes :=
  [ _root_.Gzip.mkHeader
  , _root_.Deflate.deflateStored x
  , _root_.Gzip.u32le (_root_.Gzip.crc32 x).toNat
  , _root_.Gzip.u32le (x.length % 4294967296) ]

/-- **The body's framing decomposition (spec side).** `Gzip.gzipStored x` is the
`flatten` of its fragment list — the body-grain sibling of
`Datapath.ByteRefine.serializeWire_eq`. Read straight off `gzipStored`'s definition;
the flatness is the fold calculus's doing. -/
theorem gzipStored_eq_flatten (x : Bytes) :
    _root_.Gzip.gzipStored x = (gzipFragments x).flatten := by
  show _root_.Gzip.mkHeader ++ _root_.Deflate.deflateStored x
        ++ _root_.Gzip.u32le (_root_.Gzip.crc32 x).toNat
        ++ _root_.Gzip.u32le (x.length % 4294967296)
      = (gzipFragments x).flatten
  simp [gzipFragments, List.append_assoc]

/-- **The flat body transform.** Assemble the gzip container flat: `foldAppend` over
the container fragments (one flat `Array.++` per fragment, no per-join cons-spine) —
the byte FOLD combinator (`refine_fold`) applied. This is the flat sibling of
`Gzip.gzipStored`'s `List.++`-chain. -/
def flatGzipBody (x : Bytes) : Array UInt8 :=
  foldAppend List.toArray #[] (gzipFragments x)

/-- **The flat body transform is byte-identical to `Gzip.gzipStored` — reused, not
re-proven.** `flatGzipBody x` refines `Gzip.gzipStored x`: the FOLD combinator
(`foldAppend_toArray_refines`) reads back the flatten of the fragments, and
`gzipStored_eq_flatten` collapses that to `gzipStored`. Non-vacuous: the flat op
folds real appends over the real container fragments; the bytes are proven equal,
not assumed. -/
theorem flatGzipBody_refines (x : Bytes) :
    Datapath.Refinement.Refines (_root_.Gzip.gzipStored x) (flatGzipBody x) := by
  show (flatGzipBody x).toList = _root_.Gzip.gzipStored x
  unfold flatGzipBody
  have hfold := foldAppend_toArray_refines (gzipFragments x)
  rw [show (foldAppend List.toArray #[] (gzipFragments x)).toList
        = (gzipFragments x).flatten from hfold, gzipStored_eq_flatten]

/-! ## 3. The header push IS a `refinesHdr_addHeader` (header grain) -/

/-- The flat `Content-Encoding: gzip` header push: one amortized-`O(1)` `Array.push`
onto the flat header block — the flat sibling of the deployed
`ResponseBuilder.addHeader (ceName, gzipVal)`. -/
def flatGzipHeader (h : HdrBlock) : HdrBlock := h.addHeader (ceName, gzipVal)

/-- The flat header push refines the deployed `· ++ [(ceName, gzipVal)]` — a direct
instance of the header combinator `refinesHdr_addHeader`. -/
theorem flatGzipHeader_refines :
    RefinesHdrFn (fun hs => hs ++ [(ceName, gzipVal)]) flatGzipHeader :=
  refinesHdr_addHeader (ceName, gzipVal)

/-! ## 4. The flat whole-response transform = the deployed built response -/

/-- The flat computation of the gzip-stage response: the body assembled flat by the
byte FOLD (`flatGzipBody`), the header block grown flat by the header push
(`flatGzipHeader`). The two `denote`/`.toList` boundaries (`Response.body`,
`Response.headers` are `List`-typed) are the named residual seams; the body
assembly and the header accumulation are both flat. -/
def flatGzippedResp (r : Response) : Response :=
  { r with body := (flatGzipBody r.body).toList
         , headers := (flatGzipHeader (HdrBlock.ofList r.headers)).denote }

/-- **The flat gzip response equals the deployed one — PROVEN via the two
refinements, not by definition.** The body half is `flatGzipBody_refines` (flat
fold = `gzipStored`); the header half is `denote_addHeader`/`denote_ofList` (flat
push = `++ [ce]`). -/
theorem flatGzippedResp_eq (r : Response) : flatGzippedResp r = gzippedResp r := by
  have hbody : (flatGzipBody r.body).toList = _root_.Gzip.gzipStored r.body :=
    flatGzipBody_refines r.body
  have hhdr : (flatGzipHeader (HdrBlock.ofList r.headers)).denote
      = r.headers ++ [(ceName, gzipVal)] := by
    show ((HdrBlock.ofList r.headers).addHeader (ceName, gzipVal)).denote = _
    rw [HdrBlock.denote_addHeader, HdrBlock.denote_ofList]
  unfold flatGzippedResp gzippedResp
  rw [hbody, hhdr]

/-! ## 5. Full serialize: the flat gzip stage's whole response is byte-identical -/

/-- **THE FULL BYTE-IDENTITY.** The flat gzip stage's whole serialized response
(flat body FOLD + flat header push ⟶ `Datapath.ByteRefine.flatSerialize`, the
derived flat serializer) is byte-identical to `Reactor.serialize` of the DEPLOYED
stage's response `gzippedResp`. Chains the whole-response refinement
(`flatGzippedResp_eq`) into the byte-grain serialize equality
(`flatSerialize_refines`). No deployed byte changes; the whole computation is flat
but for the named `List` seams. -/
theorem flatGzip_serialize_refines (r : Response) :
    Datapath.Refinement.Refines (Reactor.serialize (gzippedResp r))
      (flatSerialize (flatGzippedResp r)) := by
  rw [flatGzippedResp_eq]
  exact flatSerialize_refines (gzippedResp r)

/-! ## Non-vacuity — the flat ops genuinely compute, witnessed on real inputs -/

-- The flat body transform over a real body produces the REAL gzip container —
-- evaluated by the kernel (not just proven).
#guard (flatGzipBody "hi".toUTF8.toList).toList
        == _root_.Gzip.gzipStored "hi".toUTF8.toList

-- The flat body genuinely depends on the input: different bodies give different
-- flat container bytes (not a constant).
#guard (flatGzipBody "aaaa".toUTF8.toList).toList
        != (flatGzipBody "bbbbb".toUTF8.toList).toList

-- The flat gzip container is genuinely NOT the plaintext (a real transform, not a
-- passthrough): the RFC 1952 magic + trailer are present.
#guard (flatGzipBody "hi".toUTF8.toList).toList != "hi".toUTF8.toList

-- The full flat serialized response is byte-identical to the deployed serialize of
-- the deployed built response — evaluated on a real `200 OK`.
#guard (flatSerialize (flatGzippedResp (Reactor.ok200 "hi".toUTF8.toList))).data.toList
        == Reactor.serialize (gzippedResp (Reactor.ok200 "hi".toUTF8.toList))

/-! ## RESIDUAL (the honest residual for the gzip stage)

* **The container ASSEMBLY is closed here** — `mkHeader ‖ deflate ‖ CRC ‖ ISIZE`,
  proven flat (byte FOLD) and byte-identical to `Gzip.gzipStored`, plus the
  `Content-Encoding: gzip` header push (flat `Array.push`). Both grounded in the
  deployed `gzipStage.onResponse` (`gzippedResp_eq_stage`).

* **The FRAGMENT CONTENTS are the named residual.** `Gzip.deflateStored x` (the
  DEFLATE block) and `Gzip.crc32 x` (the reflected-poly CRC fold) are still `List`
  computations producing the fragment bytes; gzip's DEFLATE entropy coding and the
  CRC fold are genuine loops (the `refine_fold` residual, the exact analogue of the
  entropy-stage follow-on named in `Reactor.Stage.CompressBody`). They are NOT
  faked — the flat form here treats each as one already-materialized fragment and
  proves the CONTAINER byte-identical.

* **The `Response.body`/`Response.headers` `List` seams.** `flatGzippedResp` still
  `.toList`/`denote`s the flat `Array`/`HdrBlock` back to `List` at the
  `Response` field boundaries (the deployed `Response` is `List`-typed), the same
  seam `Datapath.FlatStage` names; closing it fully is the additive flat
  `Wire`/`serialize` variant.
-/

/-! ## Axiom audit -/

#print axioms gzippedResp_eq_stage
#print axioms gzipStored_eq_flatten
#print axioms flatGzipBody_refines
#print axioms flatGzipHeader_refines
#print axioms flatGzippedResp_eq
#print axioms flatGzip_serialize_refines

end Datapath.FlatStage_gzip
