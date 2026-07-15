import Datapath.ServeDenseIdx

/-!
# Datapath.ServeConformantDense — the CONFORMANT serve with the DENSE inner

The deployed DEFAULT serve is `Dataplane.drorbServeConformant =
Reactor.ServeConformant.conformantServe drorbServe` — the RFC-conformance wrapper
around the deployed serve. The WRAPPER is already body-dense (native `injectDateBA`
Date splice, native head-extract `x-corr` scrub, native `HEAD` truncate; the body is
never re-consed by the wrapper). But its INNER is `drorbServe` — the `List` serve —
so on every `/bulk` hit the DEFAULT deployment still materialises the 1 MiB response
body as a `List UInt8` cons-spine INSIDE the inner serve. The body-cliff the dense
serves fixed (`DRORB_SPAN=18` `serveDenseReal`, and the index-decided
`serveDenseIdx`) is LIVE in the deployed conformant default.

This module closes that: `serveConformantDenseIdx = conformantServe serveDenseIdx` —
the SAME conformance wrapper, its inner swapped for the index-decided dense serve.
Byte-identity is congruence: `conformantServe` consults its inner only pointwise
(`conformantServe_congr`), and `serveDenseIdx` is proven byte-identical to the
deployed serve (`serveDenseIdx_refines`), so the conformant-dense serve equals
`conformantServe deployedServeRef` for EVERY input — and `Dataplane` closes it to
`drorbServeConformant` where `drorbServe` is in scope
(`serveConformantDenseIdx_eq_drorbServeConformant`).

## Honest scope

* DENSE on the `/bulk` arm: the inner's arm decision (index probes, `denseArmB`),
  the head fold, the 1 MiB body (`Array` bulk-append), the wrapper's Date splice,
  scrub, and HEAD-strip (all native `ByteArray` extracts/appends).
* DENSE (inner, the head-scalar collapse): the inner's dense arm computes NO
  `input.toList` at all — constant `x-upstream` (`uvBulk`), index-native `x-corr`
  (`corrValB`), index-decided guard (`denseArmB`).
* STILL `List` (named, wrapper-inherent): `reqBytes` (`input.toList.dropWhile` — the
  wrapper's validation gate parses a `List` view of the request, O(request) cons per
  request) and `Proto.RequestSerialize.parse` over it. Removing the wrapper's own
  `List` view is the index-native `RequestSerialize.parse` rung, not claimed here.
  And the wrapper's response post-processing (`injectDateBA` splice + `scrubCorrBA`
  head-scrub reattach) each COPY the full response `ByteArray` once — ~2 extra 1 MiB
  memcpys per `/bulk` hit (measured ~47% vs the bare dense serve): the in-place /
  writev splice is the named next wrapper lever. On the dense arm the `x-corr` value
  the inner renders (O(request) dotted-decimal) is then DROPPED by the wrapper's
  scrub — fusing the wrapper with the dense arm (emit the scrubbed head directly,
  never render `x-corr`) is the named fuse rung; it needs the scrub-line lemmas over
  the concrete dense head, not claimed here.
-/

namespace Datapath.ServeConformantDense

open Reactor.ServeConformant

/-! ## Congruence — `conformantServe` consults its inner only pointwise -/

theorem acceptedRawBA_congr (A B : ByteArray → ByteArray) (h : ∀ x, A x = B x)
    (req : Proto.Request) (innerInput : ByteArray) :
    acceptedRawBA A req innerInput = acceptedRawBA B req innerInput := by
  unfold acceptedRawBA
  simp only [h]

theorem respBytesRawBA_congr (A B : ByteArray → ByteArray) (h : ∀ x, A x = B x)
    (input : ByteArray) :
    respBytesRawBA A input = respBytesRawBA B input := by
  unfold respBytesRawBA
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · exact acceptedRawBA_congr A B h _ _

/-- Pointwise-equal inners serve identical conformant bytes — `conformantServe`
never inspects its inner other than by application. -/
theorem conformantServe_congr (A B : ByteArray → ByteArray) (h : ∀ x, A x = B x)
    (input : ByteArray) :
    conformantServe A input = conformantServe B input := by
  unfold conformantServe
  rw [respBytesRawBA_congr A B h input]

/-! ## The conformant-dense serve -/

/-- **The RFC-conformant serve with the DENSE index-decided inner.** The deployed
conformance wrapper (Z1 431-gate → validation/framing gates → inner → Date splice →
`x-corr` scrub → HEAD-strip, all response-side steps native `ByteArray`) around
`Datapath.ServeDenseIdx.serveDenseIdx` — so a `GET /bulk` through the DEPLOYED
DEFAULT semantics never materialises the 1 MiB body as a `List`. -/
@[export drorb_serve_conformant_dense]
def serveConformantDenseIdx (input : ByteArray) : ByteArray :=
  conformantServe Datapath.ServeDenseIdx.serveDenseIdx input

/-- **Byte-identity to the conformant deployed serve (reference form).** For EVERY
input, the conformant-dense serve equals the conformance wrapper around the deployed
serve reference (`deployedServeRef` = `drorbServe`, closed in `Dataplane`). -/
theorem serveConformantDenseIdx_eq_ref (input : ByteArray) :
    serveConformantDenseIdx input
      = conformantServe Datapath.ServeFlatFull.deployedServeRef input :=
  conformantServe_congr _ _ Datapath.ServeDenseIdx.serveDenseIdx_refines input

/-! ## Non-vacuity — the dense arm fires through the wrapper, and the scrub bites -/

open Datapath.ServeDenseReal (bulkDemoReqAnyHost)
open Datapath.ServeDenseIdx (healthReq)

-- The conformant-dense serve on a real `/bulk` request still carries the 1 MiB body.
#guard (serveConformantDenseIdx bulkDemoReqAnyHost).size > 1048576
-- Byte-identical (kernel-evaluated) to the conformant reference serve, on-arm and off.
#guard (serveConformantDenseIdx bulkDemoReqAnyHost).data.toList
        == (conformantServe Datapath.ServeFlatFull.deployedServeRef bulkDemoReqAnyHost).data.toList
#guard (serveConformantDenseIdx healthReq).data.toList
        == (conformantServe Datapath.ServeFlatFull.deployedServeRef healthReq).data.toList
-- The wrapper scrub genuinely bites on the dense arm: the raw dense serve DOES carry
-- an `x-corr` line in its head; the conformant-dense output does NOT.
def hasCorrLine (bs : ByteArray) : Bool :=
  (bs.data.toList.take 400).zipIdx.any (fun bi => bi.1 == 120 &&
    Reactor.ServeConformant.corrPrefix.isPrefixOf (bs.data.toList.drop bi.2))

#guard hasCorrLine (Datapath.ServeDenseIdx.serveDenseIdx bulkDemoReqAnyHost)
#guard !(hasCorrLine (serveConformantDenseIdx bulkDemoReqAnyHost))

/-! ## Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms serveConformantDenseIdx_eq_ref

end Datapath.ServeConformantDense
