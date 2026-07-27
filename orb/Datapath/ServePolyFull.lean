import Datapath.ServeFlatFull
import Datapath.HdrSeq
import Datapath.ByteSeq

/-!
# Datapath.ServePolyFull — the FULL serve rendered through the POLYMORPHIC egress
fold (`[HdrSeq H]` header block + `[ByteSeq T]` body), proven BYTE-IDENTICAL to the
deployed `Dataplane.drorbServe`, and wired as `DRORB_SPAN=7`.

This is the assembly step the `ServeFlatFull` honest-scope note named as "the
composition the individually-grounded flat stages are the pieces of, still to be
chained into a fold". `servePolyFull` renders the deployed 14-stage routed response
through the **polymorphic egress algebra** — the SAME `HdrSeq`/`ByteSeq` op
vocabulary (`push`/`foldPush`, `append`) the poly stages
(`Datapath.StagePoly_*`, `Datapath.HdrSeqProto`, `Datapath.ByteSeqProto`) are built
on — instantiated at the genuinely-flat `HdrBlock`/`ByteArray`:

* the response **header block** is built by `Datapath.HdrSeq.foldPush` over the flat
  `HdrBlock` (each header pushed with the header-grain `push` op = `Array.push`,
  amortised `O(1)`, **no `List` spine**) — exactly the combinator
  `securityStagePoly`/`corsStagePoly` fold with; its denotation is `foldPush_denote`;
* the response **body** is carried as a genuine `ByteArray` and bulk-appended
  (`serializeFlatB`, R3 killed — no `body.toArray`-of-a-cons at egress).

`servePolyFull_refines` proves it produces the IDENTICAL bytes to the deployed serve
(`Datapath.ServeFlatFull.deployedServeRef`, i.e. `Dataplane.drorbServe`) for EVERY
input — both the h2c prior-knowledge fork and the full HTTP/1.1 14-stage fold.

## ★ HONEST SCOPE — what is POLY here and what is DEPLOYED-`List` fallback

Byte-identity to `servePipelineFull2 input.toList` PINS this serve to the deployed
`List` decision fold for everything that DECIDES which response is produced
(`Reactor.ServeArr.serveArr` documents the same constraint at line 40: "any function
provably equal to `servePipelineFull2 input.toList` must feed it that list"). So,
precisely:

* **POLY (flat, no cons):** the egress render — the header block (`HdrSeq.foldPush`
  over `HdrBlock`, no response-head `List` spine, K5) and the body (`ByteArray`
  bulk-append, R3). Grounded in the same op laws (`foldPush_denote`, the `HdrSeq`
  instance) the 14 `StagePoly_*` refinements are discharged from.

* **DEPLOYED-`List` fallback (unavoidable under byte-identity):**
  - the **request read** — `input.toList` (K1); the deployed pipeline re-parses it
    internally, so the index-native `parseIndexNative` cannot replace it here.
  - the **14-stage decision fold** — `Reactor.ServeArr.respOf input.toList` runs the
    real gates (jwt/basicauth/ipfilter/rate/cache/redirect/traversal/policy) and the
    handler + the body-touching transforms (**gzip CRC-32, htmlrewrite** — the 2
    body-LOOPS) in `List`, producing the `List`-typed built `Response`. The poly
    stages' whole-stage refinements are the PROVEN pieces this response is congruent
    to, but the fold itself is not re-expressed over `HdrBlock`/`ByteArray` here (that
    is the multi-file re-proof of `runPipeline`, still open).

Consequently the MEASURED win of `servePolyFull` over the deployed `List` serve is
the **egress-flattening margin only** (the same class as `ServeFlatFull`, `DRORB_SPAN=3`).
The body-dense win (`Datapath.ServeFlatBodyPoly`, `DRORB_SPAN=5`, ~5–6× on an 8 KB
body) is NOT reachable on any byte-identical-to-deployed path, because the deployed
demo app (`Reactor.Deploy.demoAppConfig`: `/health → 200 "ok"`, else `404`) produces
NO large-body route — there is no large body for the dense path to accelerate.
`servePolyFull` therefore is the honest full-poly serve; its cons-list win is the
egress margin, and this file does not overclaim the body number.
-/

namespace Datapath.ServePolyFull

open Datapath.FlatBody (serializeFlatB serializeFlatB_refines)
open Datapath.FlatHeaders (HdrBlock)
open Datapath.FlatWire (respOf)
open Datapath.HdrSeq (HdrSeq foldPush foldPush_denote)

/-! ## The polymorphic egress header block — `foldPush` over the flat `HdrBlock` -/

/-- **The response header block, built by the header-grain poly fold.** Push every
header pair of the routed response onto the empty flat `HdrBlock` with the `HdrSeq`
`push` op (`Array.push`, no `List` spine) — the identical `foldPush` combinator
`Datapath.HdrSeqProto.securityStagePoly` / `corsStagePoly` fold their fixed sets
with. Its denotation is `r.headers` (`polyHdrBlock_denote`), so rendering through it
is byte-identical to rendering `r.headers` directly. -/
def polyHdrBlock (hs : List (Proto.Bytes × Proto.Bytes)) : HdrBlock :=
  foldPush (H := HdrBlock) hs HdrSeq.empty

/-- The poly header block denotes to the header list it was folded from — a DIRECT
instance of the once-proven generic `foldPush_denote` (⇐ `push_denote`), no
`HdrBlock`-specific reasoning. -/
@[simp] theorem polyHdrBlock_denote (hs : List (Proto.Bytes × Proto.Bytes)) :
    (polyHdrBlock hs).denote = hs := by
  show HdrSeq.toHdrs (foldPush (H := HdrBlock) hs HdrSeq.empty) = hs
  rw [foldPush_denote]
  show HdrSeq.toHdrs (HdrSeq.empty : HdrBlock) ++ hs = hs
  rw [HdrSeq.empty_denote, List.nil_append]

/-! ## The per-response egress byte-identity, generalised over any denoting block -/

/-- **The flat poly egress of ANY built response is byte-identical to the deployed
`serialize`.** Generalises `Datapath.ServeFlatFull.serializeFlatB_resp` to ANY header
block `hb` whose denotation is `r.headers` (here the `foldPush`-built `polyHdrBlock`):
rendering `r` through `serializeFlatB` with `hb` + the `ByteArray` body equals
`ByteArray.mk (Reactor.serialize r).toArray`. Same equality transfer to
`serializeFlatB_refines` + the `Array.toList_inj` closer; the header hypothesis is the
denotation `hh` instead of `HdrBlock.denote_ofList`. -/
theorem serializeFlatB_resp_gen (r : Reactor.Response) (hb : HdrBlock)
    (hh : hb.denote = r.headers) :
    serializeFlatB r.status r.reason hb (ByteArray.mk r.body.toArray)
      = ByteArray.mk (Reactor.serialize r).toArray := by
  have hbody : (ByteArray.mk r.body.toArray).data.toList = r.body := by
    show r.body.toArray.toList = r.body
    rw [List.toList_toArray]
  have hkey : respOf r.status r.reason hb (ByteArray.mk r.body.toArray).data.toList = r := by
    show ({ status := r.status, reason := r.reason,
            headers := hb.denote,
            body := (ByteArray.mk r.body.toArray).data.toList } : Reactor.Response) = r
    rw [hh, hbody]
  have hlist : (serializeFlatB r.status r.reason hb (ByteArray.mk r.body.toArray)).data.toList
        = Reactor.serialize r := by
    have h := serializeFlatB_refines r.status r.reason hb (ByteArray.mk r.body.toArray)
    rw [hkey] at h
    exact h
  have hdata : (serializeFlatB r.status r.reason hb (ByteArray.mk r.body.toArray)).data
        = (Reactor.serialize r).toArray := by
    apply Array.toList_inj.mp
    rw [List.toList_toArray]; exact hlist
  show serializeFlatB r.status r.reason hb (ByteArray.mk r.body.toArray)
      = ByteArray.mk (Reactor.serialize r).toArray
  rw [← hdata]

/-! ## THE FULL POLY SERVE -/

/-- **THE FULL POLY SERVE.** Fork on the h2c connection preface exactly as the deployed
serve (drive the real H2 engine on prior knowledge); otherwise run the REAL deployed
14-stage decision fold (`Reactor.ServeArr.respOf input.toList` — jwt/basicauth/ipfilter/
rate/cache/redirect/traversal/policy gates + handler + gzip/htmlrewrite body transforms,
all producing the exact `Response` `servePipelineFull2` serializes) and render it through
the POLYMORPHIC egress: the header block folded onto the flat `HdrBlock` with the
header-grain `push` op (`polyHdrBlock`, no response-head `List` spine) and the body carried
as a genuine `ByteArray` (bulk-appended by `serializeFlatB`, no `body.toArray`-of-a-cons).
Byte-identical to the deployed serve (`servePolyFull_refines`). -/
@[export drorb_serve_poly]
def servePolyFull (input : ByteArray) : ByteArray :=
  if Reactor.Ingress.hasH2Preface input.toList then
    ByteArray.mk (Reactor.H2Ingress.serveH2c input.toList).toArray
  else
    let r := Reactor.ServeArr.respOf input.toList
    serializeFlatB r.status r.reason (polyHdrBlock r.headers) (ByteArray.mk r.body.toArray)

/-- **THE FULL POLY-SERVE BYTE-IDENTITY.** For EVERY input, the full poly serve produces
the IDENTICAL bytes to the deployed serve (`Datapath.ServeFlatFull.deployedServeRef`, i.e.
`Dataplane.drorbServe`). Both fork on the h2c preface to the same `serveH2c`; on the
HTTP/1.1 path the poly egress `serializeFlatB` of the REAL deployed built response
(`Reactor.ServeArr.respOf`, the full 14-stage fold) with the `foldPush`-built header block
is byte-identical to `ByteArray.mk (serialize thatResponse).toArray` — the exact bytes the
deployed serve emits (`servePipelineFull2 = serialize ∘ respOf`,
`Reactor.ServeArr.respOf_serialize`) — via `serializeFlatB_resp_gen` (the poly header block
denotes to `r.headers` by `polyHdrBlock_denote`). NO deployed byte changes. -/
theorem servePolyFull_refines (input : ByteArray) :
    servePolyFull input = Datapath.ServeFlatFull.deployedServeRef input := by
  unfold servePolyFull Datapath.ServeFlatFull.deployedServeRef
  by_cases h : Reactor.Ingress.hasH2Preface input.toList
  · simp only [h, if_true]
  · simp only [h, if_false, Bool.false_eq_true]
    rw [Reactor.ServeArr.respOf_serialize]
    exact serializeFlatB_resp_gen (Reactor.ServeArr.respOf input.toList)
      (polyHdrBlock (Reactor.ServeArr.respOf input.toList).headers)
      (polyHdrBlock_denote _)

/-! ## Non-vacuity — a concrete real request through the full poly serve, evaluated -/

/-- A real `GET /health` request (routes to the deployed handler, not an echo). -/
def demoReq : ByteArray := "GET /health HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

-- The full poly serve produces a genuine deployed response (non-empty, routed).
#guard (servePolyFull demoReq).size > 0
-- The full poly serve is byte-identical to the deployed serve on the real request
-- (kernel-evaluated — the full 14-stage fold, poly egress).
#guard (servePolyFull demoReq).data.toList == (Datapath.ServeFlatFull.deployedServeRef demoReq).data.toList
-- Genuine dependence on the request: a different target routes differently.
#guard (servePolyFull demoReq).data.toList
        != (servePolyFull "GET /nope HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8).data.toList
-- The poly header block is the same header-grain fold the poly stages use, and it
-- denotes to the routed response's headers (the egress is poly, not a re-spec).
#guard (polyHdrBlock [("a".toUTF8.toList, "1".toUTF8.toList)]).denote
        == [("a".toUTF8.toList, "1".toUTF8.toList)]

/-! ## Axiom audit -/

#print axioms servePolyFull_refines

end Datapath.ServePolyFull
