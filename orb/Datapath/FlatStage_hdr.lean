import Datapath.FlatHeaders
import Datapath.ByteRefine
import Reactor.Deploy

/-!
# Datapath.FlatStage_hdr — the deployed header-stamp stage proven flat,
byte-identical to its `List` form.

The target is `Reactor.Deploy.headerRewriteStage` — stage **8** of
`deployStagesFull2`, the deploy header-stamp that installs the fixed response
headers `Server` (`Lifecycle.stdRewrite`), `x-upstream` (the proxy/DNS-chosen
backend) and `x-corr` (the `Trace` correlation id). On the response phase it
runs the REAL `Header.run` program `deployProg` through the affine builder's
`mapResp` (`Reactor.Lifecycle.rewriteResp`).

## Why this stage is NOT a push-fold (the honest re-scope)

The `securityheaders`/`cors` exemplars (`Datapath.FlatStage`,
`Datapath.FlatStage_cors`) are pure header APPENDS: their whole effect is
`hs ++ xs` for a fixed `xs`, discharged in one line by
`refinesHdr_foldAddHeader`. **The deploy header stamp is not.** `deployProg`
runs `Header.run [hopDyn, set Server, set x-upstream, set x-corr]`, and
`Header.set` = `remove` (a `filter` that DROPS existing fields of that name)
`++ [⟨n,v⟩]`, while `hopDyn` STRIPS the RFC 9110 §7.6.1 hop-by-hop set. A strip
and a replace are not a monotone append `hs ++ xs`, so `refinesHdr_foldAddHeader`
does not apply and mirroring `flatSecurityStage` verbatim is impossible.

What this stage needs instead — and what this file supplies — is a flat
`Header.run` **over the flat block**: `aRemove`/`aStrip`/`aSet` run the strip and
the replace as `Array.filter`/`Array.push` on the contiguous
`Array (Bytes × Bytes)`, so a whole program threads the block flat with no
per-op cons-spine copy, and `toHeaders_aRun` proves the flat run agrees with the
deployed `Header.run` on the denotation. This is the genuine flat form of a
strip+set stage; it is a strictly larger obligation than a push-fold (a whole
flat `Header.run`, not one `foldl`), which is the precise re-scope from the
confirmed push-fold recipe.

## What is proven here (equality-transfer, NOT a re-spec)

* `deployHdrStage_headers_effect` — the *deployed* stage's net effect on the
  built response header block is exactly
  `ofHeaders (Header.run (deployProg …) (toHeaders hs))`, read off the real
  `headerRewriteStage.onResponse` (its `mapResp (rewriteResp (deployProg …))`)
  via `Reactor.Pipeline.build_mapResp`. The effect is grounded, not re-specified.
* `toHeaders_aRun` — the flat `Header.run` (`aRun`, `Array.filter`/`Array.push`)
  denotes to the deployed `Header.run` on the denotation, for ANY program and
  block: the flat crux, the strip+set sibling of `HdrBlock.denote_foldAddHeader`.
* `flatDeployHdrStage` + `flatDeployHdrStage_refines` — the flat form runs the
  REAL `deployProg` flat on the block and is proven to compute the SAME header
  block the deployed stage builds. Non-vacuous: the flat ops genuinely filter and
  push; the content is proven equal, not assumed.
* `flatDeployHdrStage_render_byte_identical` — the flat block rendered is
  byte-identical to `Reactor.renderHeaders` of the deployed stage's header block
  (`flatRenderBlock_refines`).
* `flatDeployHdr_serialize_refines` — the full serialized response of the flat
  stage is byte-identical to `Reactor.serialize` of the deployed stage's response,
  chaining the header-block equality into the derived flat serializer
  `Datapath.ByteRefine.flatSerialize`.
* `flatDeployHdrResp_is_deployResp` — ties the flat response to the ACTUAL
  deployed `Reactor.Deploy.deployResp` (not a toy program), so this is the real
  deploy header stage, flat.
-/

namespace Datapath.FlatStage_hdr

open Proto (Bytes)
open Reactor (Response)
open Reactor.Pipeline (Ctx ResponseBuilder build_mapResp)
open Reactor.Deploy (headerRewriteStage deployProg deployPlan deploySubs)
open Datapath.FlatHeaders
open Datapath.Refinement

/-! ## 0. Bridge lemmas: `toHeaders`/`ofHeaders` over `filter`/`append`, and the
`Array` ↔ `List` `filter`/`push` bridges. -/

/-- Filtering commutes with a map (the head-case-split identity). -/
private theorem map_comm_filter {α β} (g : α → β) (q : β → Bool) (l : List α) :
    (l.map g).filter q = (l.filter (fun x => q (g x))).map g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases h : q (g a) = true
    · simp [h, ih]
    · simp [h, ih]

/-- `toHeaders` pushes through a `filter`: filtering the field view equals viewing
the filtered pairs (the predicate transported across the `⟨p.1, p.2⟩` view). -/
private theorem toHeaders_filter (q : Header.Field → Bool) (l : List (Bytes × Bytes)) :
    (Reactor.Lifecycle.toHeaders l).filter q
      = Reactor.Lifecycle.toHeaders (l.filter (fun p => q ⟨p.1, p.2⟩)) := by
  unfold Reactor.Lifecycle.toHeaders
  rw [map_comm_filter]

/-- `toHeaders` distributes over `++`. -/
private theorem toHeaders_append (l m : List (Bytes × Bytes)) :
    Reactor.Lifecycle.toHeaders (l ++ m)
      = Reactor.Lifecycle.toHeaders l ++ Reactor.Lifecycle.toHeaders m := by
  unfold Reactor.Lifecycle.toHeaders; rw [List.map_append]

/-- `ofHeaders ∘ toHeaders = id` — the field view round-trips (both maps are the
identity on the `(name, value)` pair). -/
private theorem ofHeaders_toHeaders (l : List (Bytes × Bytes)) :
    Reactor.Lifecycle.ofHeaders (Reactor.Lifecycle.toHeaders l) = l := by
  unfold Reactor.Lifecycle.ofHeaders Reactor.Lifecycle.toHeaders
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, List.map_cons, ih]

/-! ## 1. The flat `Header.run` over the flat block (filter + push) -/

/-- Flat `remove`: drop every pair whose name matches `n`, as one `Array.filter`
(no cons-spine copy). Denotes to `Header.remove`. -/
def aRemove (n : Header.Name) (a : Array (Bytes × Bytes)) : Array (Bytes × Bytes) :=
  a.filter (fun p => !Header.nameEqb p.1 n)

/-- Flat hop-by-hop strip: drop every pair whose name is in the hop set, as one
`Array.filter`. Denotes to `Header.strip`. -/
def aStrip (hop : List Header.Name) (a : Array (Bytes × Bytes)) : Array (Bytes × Bytes) :=
  a.filter (fun p => !Header.isHop hop p.1)

/-- Flat interpretation of one `Header.Op` on the flat block — the strip/replace
run as `Array.filter`/`Array.push`. The flat sibling of `Header.applyOp`. -/
def aApplyOp (o : Header.Op) (a : Array (Bytes × Bytes)) : Array (Bytes × Bytes) :=
  match o with
  | .set n v  => (aRemove n a).push (n, v)
  | .remove n => aRemove n a
  | .add n v  => a.push (n, v)
  | .hop names => aStrip names a
  | .hopDyn   => aStrip (Header.dynHopSet (Reactor.Lifecycle.toHeaders a.toList)) a

/-- Flat `Header.run`: fold the program over the flat block, each op a
`filter`/`push` (the block threads flat, no per-op spine copy). -/
def aRun (prog : List Header.Op) (a : Array (Bytes × Bytes)) : Array (Bytes × Bytes) :=
  prog.foldl (fun acc o => aApplyOp o acc) a

private theorem toHeaders_aRemove (n : Header.Name) (a : Array (Bytes × Bytes)) :
    Reactor.Lifecycle.toHeaders (aRemove n a).toList
      = Header.remove n (Reactor.Lifecycle.toHeaders a.toList) := by
  unfold aRemove
  simp only [Array.toList_filter]
  rw [Header.remove, toHeaders_filter]

private theorem toHeaders_aStrip (hop : List Header.Name) (a : Array (Bytes × Bytes)) :
    Reactor.Lifecycle.toHeaders (aStrip hop a).toList
      = Header.strip hop (Reactor.Lifecycle.toHeaders a.toList) := by
  unfold aStrip
  simp only [Array.toList_filter]
  rw [Header.strip, toHeaders_filter]

/-- **One flat op = the deployed op on the denotation.** For any op and block, the
flat `aApplyOp` denotes to the deployed `Header.applyOp` on the block's
denotation. -/
private theorem toHeaders_aApplyOp (o : Header.Op) (a : Array (Bytes × Bytes)) :
    Reactor.Lifecycle.toHeaders (aApplyOp o a).toList
      = Header.applyOp o (Reactor.Lifecycle.toHeaders a.toList) := by
  cases o with
  | set n v =>
    show Reactor.Lifecycle.toHeaders ((aRemove n a).push (n, v)).toList = Header.set n v _
    rw [Array.toList_push, toHeaders_append, toHeaders_aRemove]
    rfl
  | remove n => exact toHeaders_aRemove n a
  | add n v =>
    show Reactor.Lifecycle.toHeaders (a.push (n, v)).toList = Header.add n v _
    rw [Array.toList_push, toHeaders_append]
    rfl
  | hop names => exact toHeaders_aStrip names a
  | hopDyn =>
    show Reactor.Lifecycle.toHeaders
        (aStrip (Header.dynHopSet (Reactor.Lifecycle.toHeaders a.toList)) a).toList = _
    rw [toHeaders_aStrip]
    rfl

/-- **THE FLAT CRUX.** The flat `Header.run` (`aRun`, all `filter`/`push`) denotes
to the deployed `Header.run` on the block's denotation, for ANY program and block.
The strip+set sibling of `HdrBlock.denote_foldAddHeader`, and what the flat deploy
header stage rides on. -/
theorem toHeaders_aRun (prog : List Header.Op) (a : Array (Bytes × Bytes)) :
    Reactor.Lifecycle.toHeaders (aRun prog a).toList
      = Header.run prog (Reactor.Lifecycle.toHeaders a.toList) := by
  induction prog generalizing a with
  | nil => rfl
  | cons o rest ih =>
    have hstep : aRun (o :: rest) a = aRun rest (aApplyOp o a) := by
      simp [aRun, List.foldl_cons]
    rw [hstep, ih, Header.run_cons, toHeaders_aApplyOp]

/-! ## 2. The flat stage, grounded in the deployed `headerRewriteStage` -/

/-- **The deployed `headerRewriteStage`'s net header effect — grounded, not
re-specified.** For any context and any incoming builder, the BUILT response of
the real stage has header block
`ofHeaders (Header.run (deployProg …) (toHeaders b.build.headers))` — read off the
stage's `mapResp (rewriteResp (deployProg …))` via `build_mapResp`. This is the
function the flat form must compute. -/
theorem deployHdrStage_headers_effect (c : Ctx) (b : ResponseBuilder) :
    ((headerRewriteStage.onResponse c b).build).headers
      = Reactor.Lifecycle.ofHeaders
          (Header.run (deployProg (deployPlan (deploySubs c.input)) c.input)
            (Reactor.Lifecycle.toHeaders b.build.headers)) := by
  show ((b.mapResp
      (Reactor.Lifecycle.rewriteResp
        (deployProg (deployPlan (deploySubs c.input)) c.input))).build).headers = _
  rw [build_mapResp]
  rfl

/-- **The flat deploy header stage.** Runs the REAL `deployProg` flat over the
block: strip the hop set and install `Server`/`x-upstream`/`x-corr` by
`Array.filter`/`Array.push`, no per-op cons-spine copy. The flat sibling of the
deployed stage's `Header.run (deployProg …)`. -/
def flatDeployHdrStage (prog : List Header.Op) (h : HdrBlock) : HdrBlock :=
  ⟨aRun prog h.headers⟩

/-- The flat stage's denotation is exactly the deployed `Header.run` header
block — PROVEN via `toHeaders_aRun`, not by definition. -/
theorem flatDeployHdrStage_denote (prog : List Header.Op) (h : HdrBlock) :
    (flatDeployHdrStage prog h).denote
      = Reactor.Lifecycle.ofHeaders (Header.run prog (Reactor.Lifecycle.toHeaders h.denote)) := by
  show (aRun prog h.headers).toList
      = Reactor.Lifecycle.ofHeaders (Header.run prog (Reactor.Lifecycle.toHeaders h.headers.toList))
  rw [← ofHeaders_toHeaders (aRun prog h.headers).toList, toHeaders_aRun]

/-- **The flat stage computes the deployed stage's header block.** Running the flat
`deployProg` over the flat view of a base header list yields exactly the header
block `deployHdrStage_headers_effect` reads off the deployed
`headerRewriteStage`. Non-vacuous: the flat ops genuinely filter and push; the
content is proven equal, not assumed. -/
theorem flatDeployHdrStage_refines (c : Ctx) (b : ResponseBuilder) :
    (flatDeployHdrStage (deployProg (deployPlan (deploySubs c.input)) c.input)
        (HdrBlock.ofList b.build.headers)).denote
      = ((headerRewriteStage.onResponse c b).build).headers := by
  rw [flatDeployHdrStage_denote, HdrBlock.denote_ofList, deployHdrStage_headers_effect]

/-! ## 3. Byte-identical: flat render = deployed render -/

/-- **The flat stage's rendered header bytes are byte-identical to the deployed
stage's.** The flat block after the deploy header run, rendered through the flat
renderer, equals `Reactor.renderHeaders` of exactly the header block
`flatDeployHdrStage_denote` produces — `flatRenderBlock_refines` on the flat
stage's output. -/
theorem flatDeployHdrStage_render_byte_identical (prog : List Header.Op) (h : HdrBlock) :
    Datapath.Refinement.Refines
      (Reactor.renderHeaders
        (Reactor.Lifecycle.ofHeaders (Header.run prog (Reactor.Lifecycle.toHeaders h.denote))))
      (flatRenderBlock (flatDeployHdrStage prog h)) := by
  have hr := flatRenderBlock_refines (flatDeployHdrStage prog h)
  rwa [flatDeployHdrStage_denote] at hr

/-! ## 4. Full serialize: the flat stage's whole response is byte-identical -/

/-- The flat computation of the deploy-header-stage response: run the deploy header
program flat over the block (`flatDeployHdrStage`), then present it for
serialization. The single `denote` (Array → List) at the `Response.headers`
boundary is the shared residual seam (as in `Datapath.FlatStage`); the header run
and the serialization are both flat. -/
def flatDeployHdrResp (prog : List Header.Op) (r : Response) : Response :=
  { r with headers := (flatDeployHdrStage prog (HdrBlock.ofList r.headers)).denote }

/-- The flat deploy-header response equals the deployed `rewriteResp` one — PROVEN
via the flat-run = deployed-run denotation equality, not by definition. -/
theorem flatDeployHdrResp_eq (prog : List Header.Op) (r : Response) :
    flatDeployHdrResp prog r = Reactor.Lifecycle.rewriteResp prog r := by
  have hh : (flatDeployHdrStage prog (HdrBlock.ofList r.headers)).denote
      = Reactor.Lifecycle.ofHeaders (Header.run prog (Reactor.Lifecycle.toHeaders r.headers)) := by
    rw [flatDeployHdrStage_denote, HdrBlock.denote_ofList]
  show { r with headers := (flatDeployHdrStage prog (HdrBlock.ofList r.headers)).denote }
      = { r with headers := Reactor.Lifecycle.ofHeaders (Header.run prog (Reactor.Lifecycle.toHeaders r.headers)) }
  rw [hh]

/-- **THE FULL BYTE-IDENTITY.** The flat deploy-header stage's whole serialized
response (flat `Header.run` ⟶ `Datapath.ByteRefine.flatSerialize`) is
byte-identical to `Reactor.serialize` of the DEPLOYED stage's response
(`Reactor.Lifecycle.rewriteResp prog`). Chains `flatDeployHdrResp_eq` into the
byte-grain serialize equality `flatSerialize_refines`. -/
theorem flatDeployHdr_serialize_refines (prog : List Header.Op) (r : Response) :
    Datapath.Refinement.Refines
      (Reactor.serialize (Reactor.Lifecycle.rewriteResp prog r))
      (flatSerialize (flatDeployHdrResp prog r)) := by
  rw [flatDeployHdrResp_eq]
  exact flatSerialize_refines (Reactor.Lifecycle.rewriteResp prog r)

/-- **Ties the flat form to the ACTUAL deployed `deployResp`.** For any input, the
flat deploy-header response over the real base application response is exactly
`Reactor.Deploy.deployResp input` — so this file flats the genuine deployed header
stage, not a toy program. -/
theorem flatDeployHdrResp_is_deployResp (input : Bytes) :
    flatDeployHdrResp (deployProg (deployPlan (deploySubs input)) input)
        (Reactor.demoResp (deploySubs input)) = Reactor.Deploy.deployResp input := by
  rw [flatDeployHdrResp_eq]
  rfl

/-! ## Non-vacuity — the flat run genuinely strips and installs, witnessed on real
inputs. Uses `Lifecycle.stdRewrite` (`[hopDyn, set Server drorb]`) as a concrete
computable sub-program of `deployProg`; the general theorems above are stated over
the full real `deployProg`. -/

/-- `Connection: close` — a hop-by-hop header the strip must drop. -/
def connF : Bytes × Bytes := ([67, 111, 110, 110, 101, 99, 116, 105, 111, 110], [99, 108, 111, 115, 101])

/-- `X-Trace: 1` — an end-to-end header the strip must keep. -/
def xtF : Bytes × Bytes := ([88, 45, 84, 114, 97, 99, 101], [49])

-- The flat run genuinely strips the hop header and installs `Server: drorb`
-- (kernel-evaluated): `Connection` gone, `X-Trace` kept, `Server` appended.
#guard (flatDeployHdrStage Reactor.Lifecycle.stdRewrite (HdrBlock.ofList [connF, xtF])).denote
        == [xtF, (Reactor.Lifecycle.serverName, Reactor.Lifecycle.serverVal)]

-- The flat run genuinely CHANGES the header block (a real strip+set, not identity).
#guard (flatDeployHdrStage Reactor.Lifecycle.stdRewrite (HdrBlock.ofList [connF, xtF])).denote
        != [connF, xtF]

-- The flat run computes exactly the deployed `Header.run` header block — evaluated.
#guard (flatDeployHdrStage Reactor.Lifecycle.stdRewrite (HdrBlock.ofList [connF, xtF])).denote
        == Reactor.Lifecycle.ofHeaders
            (Header.run Reactor.Lifecycle.stdRewrite (Reactor.Lifecycle.toHeaders [connF, xtF]))

-- The full flat serialized response is byte-identical to the deployed serialize —
-- evaluated on a real `200 OK` carrying a hop header.
#guard (flatSerialize (flatDeployHdrResp Reactor.Lifecycle.stdRewrite
          { status := 200, reason := [79, 75], headers := [connF, xtF], body := [104, 105] })).data.toList
        == Reactor.serialize (Reactor.Lifecycle.rewriteResp Reactor.Lifecycle.stdRewrite
          { status := 200, reason := [79, 75], headers := [connF, xtF], body := [104, 105] })

/-! ## Axiom audit -/

#print axioms toHeaders_aRun
#print axioms deployHdrStage_headers_effect
#print axioms flatDeployHdrStage_refines
#print axioms flatDeployHdrStage_render_byte_identical
#print axioms flatDeployHdr_serialize_refines
#print axioms flatDeployHdrResp_is_deployResp

end Datapath.FlatStage_hdr
