import Datapath.ByteSeq
import Datapath.HdrSeq
import Datapath.FlatStage_gzip

/-!
# Datapath.StagePoly_gzip — the deployed `gzip` stage (position 10 of
`Reactor.Deploy.deployStagesFull2`) written ByteSeq/HdrSeq-POLYMORPHIC, with each
half's whole-stage refinement FOLLOWING from the op laws (~1 line each), grounded
in the REAL deployed `Reactor.Stage.Gzip.gzipStage.onResponse`.

The `gzip` stage crosses TWO grains (like the serve): on a gzip-accepting request
its `onResponse` (read off `gzipStage`) does

* a BODY rewrite — `body ⟶ Gzip.gzipStored r.body`, the RFC 1952 container
  `mkHeader ‖ deflateStored r.body ‖ CRC-32 ‖ ISIZE`; and
* a HEADER push — `headers ⟶ r.headers ++ [(ceName, gzipVal)]`
  (`Content-Encoding: gzip`).

So it is the two-grain sibling of `Datapath.ByteSeqProto.servePoly` (body/container,
`[ByteSeq T]`) + `Datapath.HdrSeqProto.corsStagePoly` (single-header push,
`[HdrSeq H]`). Each half is ONE polymorphic expression whose `<half>Poly_refines` is
a single `simp` over the op laws (`foldCat_denote` / `foldPush_denote`) — NO
per-stage induction, NO re-expression of the stage — then GROUNDED in the deployed
stage via the already-proven `Datapath.FlatStage_gzip` bridge lemmas
(`gzippedResp_eq_stage`, `gzipStored_eq_flatten`), instantiated at `List` (spec) and
`ByteArray`/`HdrBlock` (fast, genuinely flat).

## What fit the simp pattern, and what did NOT (the honest residual)

* **HEADER push (`gzipHeaderPoly`, `[HdrSeq H]`)** — fits exactly like
  `corsStagePoly`: `foldPush [(ceName, gzipVal)]`; refinement one line off
  `foldPush_denote`/`foldPush_list`.
* **BODY CONTAINER assembly (`gzipBodyPoly`, `[ByteSeq T]`)** — fits exactly like
  `servePoly`: the `mkHeader ‖ deflate ‖ CRC ‖ ISIZE` concatenation is a `foldCat`
  over the container fragments; refinement one line off `foldCat_denote`/`foldCat_list`.
  `deflateStored x` here is a SINGLE stored block (`0x01 :: u16le len ++ u16le nlen
  ++ x`, `Deflate.deflateStored`) — straight-line framing, so it folds in as one
  fragment.
* **★ THE BODY LOOP — the honest residual (NOT faked).** The only genuine byte-LOOP
  in the body is `Gzip.crc32 x`: a reflected-poly CRC-32 fold whose accumulator is a
  `UInt32` SCALAR, not a byte sequence — it does NOT fit a `[ByteSeq T]` combinator
  (`foldCat` folds byte-sequences into a byte-sequence; crc32 folds bytes into a
  register). It resists the container simp and is named here as residual, treated as
  one already-materialized fragment (exactly the residual `Datapath.FlatStage_gzip`
  and `Reactor.Stage.CompressBody` name). A ByteSeq loop combinator was ATTEMPTED and
  does not fit: the CRC state is not a `ByteSeq`.
-/

namespace Datapath.StagePoly_gzip

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx ResponseBuilder)
open Reactor.Stage.Gzip (gzipStage ceName gzipVal acceptsGzip)
open Datapath.ByteSeq
open Datapath.HdrSeq
open Datapath.FlatHeaders (HdrBlock)
open Datapath.FlatStage_gzip (gzippedResp gzippedResp_eq_stage gzipFragments gzipStored_eq_flatten)

/-! ## 1. HEADER grain — the `Content-Encoding: gzip` push, ONCE over `[HdrSeq H]` -/

/-- **The gzip header push, written ONCE over `[HdrSeq H]`.** Fold the single
`Content-Encoding: gzip` pair (`(ceName, gzipVal)`, read off the deployed
`gzipStage.onResponse`'s `addHeader`) onto the header block with `push` — the
one-header sibling of `corsStagePoly`. -/
def gzipHeaderPoly {H : Type} [HdrSeq H] (h : H) : H :=
  foldPush [(ceName, gzipVal)] h

/-- **The header-half refinement — FOLLOWS from the op laws.** One-line `simp` over
`foldPush_denote` (⇐ `push_denote`); no per-stage induction. -/
theorem gzipHeaderPoly_refines {H : Type} [HdrSeq H] (h : H) :
    HdrSeq.toHdrs (gzipHeaderPoly h)
      = gzipHeaderPoly (H := List (Bytes × Bytes)) (HdrSeq.toHdrs h) := by
  simp only [gzipHeaderPoly, foldPush_denote, foldPush_list]

/-- The header refinement at the fast `HdrBlock` instance — a DIRECT instance. -/
theorem gzipHeaderBlock_refines (h : HdrBlock) :
    HdrBlock.denote (gzipHeaderPoly h)
      = gzipHeaderPoly (H := List (Bytes × Bytes)) h.denote :=
  gzipHeaderPoly_refines h

/-- **Grounded in the REAL deployed stage (non-vacuous).** On a gzip-accepting
request the poly header push at the spec instance computes exactly the deployed
`gzipStage.onResponse`'s built header block — via the deployed bridge
`gzippedResp_eq_stage`, not a re-spec. -/
theorem gzipHeaderPoly_eq_deployed (c : Ctx) (b : ResponseBuilder)
    (h : acceptsGzip c.req = true) :
    gzipHeaderPoly (H := List (Bytes × Bytes)) b.build.headers
      = ((gzipStage.onResponse c b).build).headers := by
  rw [gzipHeaderPoly, foldPush_list, gzippedResp_eq_stage c b h]
  rfl

/-! ## 2. BODY grain — the RFC 1952 container assembly, ONCE over `[ByteSeq T]` -/

/-- **The gzip container assembly, written ONCE over `[ByteSeq T]`.** Fold the
container fragments (`mkHeader ‖ deflateStored ‖ CRC-32 ‖ ISIZE`, the
`gzipFragments` read off `Gzip.gzipStored`'s `++`-chain) with `append` — the
body-container sibling of `servePoly`. The fragment CONTENTS are `List`-carried
(the residual, see the header note); the CONTAINER concatenation is flat. -/
def gzipBodyPoly {T : Type} [ByteSeq T] (frags : List T) : T :=
  foldCat frags

/-- **The body-half refinement — FOLLOWS from the op laws.** One-line `simp` over
`foldCat_denote`/`foldCat_list`; no per-stage induction, no re-expression. -/
theorem gzipBodyPoly_refines {T : Type} [ByteSeq T] (frags : List T) :
    ByteSeq.toBytes (gzipBodyPoly frags)
      = gzipBodyPoly (T := List UInt8) (frags.map ByteSeq.toBytes) := by
  simp only [gzipBodyPoly, foldCat_denote, foldCat_list]

/-- The body refinement at the fast `ByteArray` instance — a DIRECT instance. -/
theorem gzipBodyArray_refines (frags : List ByteArray) :
    (gzipBodyPoly frags).data.toList
      = gzipBodyPoly (T := List UInt8) (frags.map (·.data.toList)) :=
  gzipBodyPoly_refines frags

/-- **Grounded in the REAL deployed stage (non-vacuous).** On a gzip-accepting
request the poly container at the spec instance, fed the deployed
`gzipFragments b.build.body`, computes exactly the deployed stage's built body
`Gzip.gzipStored b.build.body` — via `foldCat_list` + `gzipStored_eq_flatten`
(the framing decomposition) + the deployed bridge `gzippedResp_eq_stage`. Grounded,
not re-specified. -/
theorem gzipBodyPoly_eq_deployed (c : Ctx) (b : ResponseBuilder)
    (h : acceptsGzip c.req = true) :
    gzipBodyPoly (T := List UInt8) (gzipFragments b.build.body)
      = ((gzipStage.onResponse c b).build).body := by
  rw [gzipBodyPoly, foldCat_list, ← gzipStored_eq_flatten, gzippedResp_eq_stage c b h]
  rfl

/-! ## Non-vacuity — the poly forms genuinely compute the REAL deployed effect
at BOTH instances (evaluated by the kernel, not just proven). -/

-- HEADER, flat `HdrBlock`: the poly push lands the deployed `Content-Encoding: gzip`.
#guard (gzipHeaderPoly (HdrBlock.ofList [("X-A".toUTF8.toList, "1".toUTF8.toList)])).denote
        == [("X-A".toUTF8.toList, "1".toUTF8.toList)] ++ [(ceName, gzipVal)]

-- HEADER genuinely pushes (empty ⟶ the single ce pair).
#guard (gzipHeaderPoly (HdrBlock.ofList [])).denote == [(ceName, gzipVal)]

-- HEADER: spec and flat instances agree on a concrete input (the refinement, run).
#guard (gzipHeaderPoly (HdrBlock.ofList [("H".toUTF8.toList, "v".toUTF8.toList)])).denote
        == gzipHeaderPoly (H := List (Bytes × Bytes)) [("H".toUTF8.toList, "v".toUTF8.toList)]

-- BODY, flat `ByteArray`: the poly container over the REAL deployed fragments is
-- byte-identical to the deployed `Gzip.gzipStored` of the body.
#guard (gzipBodyPoly ((gzipFragments "hi".toUTF8.toList).map (fun l => (⟨l.toArray⟩ : ByteArray)))).data.toList
        == _root_.Gzip.gzipStored "hi".toUTF8.toList

-- BODY genuinely depends on the input: different bodies ⟶ different container bytes.
#guard (gzipBodyPoly ((gzipFragments "aaaa".toUTF8.toList).map (fun l => (⟨l.toArray⟩ : ByteArray)))).data.toList
        != (gzipBodyPoly ((gzipFragments "bbbbb".toUTF8.toList).map (fun l => (⟨l.toArray⟩ : ByteArray)))).data.toList

-- BODY is genuinely NOT the plaintext (the RFC 1952 container is a real transform).
#guard (gzipBodyPoly ((gzipFragments "hi".toUTF8.toList).map (fun l => (⟨l.toArray⟩ : ByteArray)))).data.toList
        != "hi".toUTF8.toList

-- BODY: spec and flat instances agree on a concrete input (the refinement, run).
#guard (gzipBodyPoly ((gzipFragments "body".toUTF8.toList).map (fun l => (⟨l.toArray⟩ : ByteArray)))).data.toList
        == gzipBodyPoly (T := List UInt8) (gzipFragments "body".toUTF8.toList)

-- The container fold at spec IS the deployed body bytes (grounding, evaluated).
#guard (gzipBodyPoly (T := List UInt8) (gzipFragments "hi".toUTF8.toList))
        == _root_.Gzip.gzipStored "hi".toUTF8.toList

/-! ## RESIDUAL (the honest residual for the gzip stage, this pass)

* **HEADER push + BODY CONTAINER assembly: CLOSED.** Both are ONE polymorphic
  expression whose refinement is a single `simp` over the op laws (`foldPush_denote`
  / `foldCat_denote`), grounded in the deployed `gzipStage.onResponse` via
  `gzippedResp_eq_stage` (no re-spec).

* **★ THE BODY LOOP (`Gzip.crc32`) is the named residual — NOT faked.** The CRC-32
  fold accumulates into a `UInt32` register, not a byte sequence, so it does NOT fit
  a `[ByteSeq T]` combinator (a ByteSeq loop combinator was attempted and does not
  match: `foldCat` folds byte-sequences, crc32's state is a scalar). It is treated as
  one already-materialized fragment; the CONTAINER around it is proven flat and
  byte-identical. `deflateStored` here is a single straight-line stored block (no
  chunking loop), so it too folds in as one fragment. This is the exact
  `refine_fold` residual `Datapath.FlatStage_gzip` and `Reactor.Stage.CompressBody`
  name.

* **The `Response.body`/`Response.headers` `List` seams** at the field boundaries are
  the same denotation seams every `FlatStage_*` names; unchanged here.
-/

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}. -/

#print axioms gzipHeaderPoly_refines
#print axioms gzipHeaderPoly_eq_deployed
#print axioms gzipBodyPoly_refines
#print axioms gzipBodyPoly_eq_deployed

end Datapath.StagePoly_gzip
