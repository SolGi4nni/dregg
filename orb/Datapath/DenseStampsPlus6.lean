import Datapath.DenseStampsPlus5
import Reactor.DeployPlus6

/-!
# Datapath.DenseStampsPlus6 — the DEPLOYED DEFAULT moves to the plus6 fold,
keeping the dense `/bulk` arm

`Reactor.DeployPlus6` extends the deployed default with three un-inerted
stages (the dispatch-scoped `405` method allow-list, the
`multipart/byteranges` `206`) and three built-from-missing features (the
CL+TE-conflict `400`, the negotiated `/welcome` i18n route, the `/dashboard`
ops page). This module carries that fold to the HOST's default crossing
WITHOUT re-opening the `/bulk` body-cliff:

* `armB6` — the plus6 dense guard: ONE index-native head parse deciding the
  plus5 guard's conjuncts (`ReqArm ∧ OffEdges`) AND the new `OffEdges6`
  conjuncts (all six new stages provably transparent on the request).
* `serveMeteredPlus6HeadIdx` — the deployed-rung metered serve: a firing
  guard emits the EXACT plus5 dense assembly (fully-stamped dense head +
  dense 1 MiB body — reused verbatim, its proof stack untouched); everything
  else is the plus6 metered `List` fold.
* `serveMeteredPlus6HeadIdx_eq` — **the byte-identity**: for EVERY
  `(peer, seq, input)` it equals `drorbServeMeteredPlus6`. The firing case
  composes the plus5 dense byte-identity (`plus5DenseArm_eq`, reused) with
  the plus6 conservation theorem (`plus6_collapse`: off the new edges the
  plus6 fold IS the plus5 fold).
* `serveMeteredPlus6HeadIdxConformant` — the RFC-conformant wrapper, proven
  equal to `drorbServeMeteredPlus6Conformant` for every input.

## The host symbol

The host's default metered crossing is the fixed C symbol
`drorb_serve_metered_plus5_dense_conformant` (declared in the host's serve
seam, owned by another workstream — not edited here). This module now OWNS
that export: the symbol keeps its ABI and its conformance wrapper but serves
the PLUS6 fold — default-on, no env lever (`DRORB_PLUS5=0` still reverts the
host to the plus4 fold). The honest-named alias
`drorb_serve_metered_plus6_dense_conformant` is exported alongside for the
host's next re-point; the plus5-named symbol is a NAMED RESIDUAL until the
host seam's owner renames its extern declaration.

Residuals (named): the guard performs one extra head-sized decide set per
request over the plus5 guard (index-native, never the body); a genuinely
multi-ranged `/bulk` request leaves the dense arm (correct — its answer is
the multipart `206`, a different byte string, served by the `List` fold).
-/

namespace Datapath.DenseStampsPlus6

open Proto (Bytes)
open Reactor (Response serialize)
open Reactor.Pipeline (Ctx runPipeline)
open Reactor.Deploy
open Reactor.DeployPlus5 (servePipelinePlus5Metered deployRespPlus5Of)
open Reactor.DeployPlus6 (deployStagesPlus6 drorbServeMeteredPlus6
  drorbServeMeteredPlus6Conformant servePipelinePlus6Metered
  deployRespPlus6Of plus6_collapse)
open Reactor.Stage.MethodFilter (isAllowed)
open Reactor.Stage.ClTeGuard (clTeConflict)
open Reactor.Stage.MultiRange (rangesOf)
open Reactor.Stage.ContentLanguage (welcomeTarget)
open Reactor.Stage.Dashboard (dashTarget)
open Datapath.SpanBytes (full full_wf read_eq_denote denote_full
  parseIndexNative parseIndexNative_refines)
open Datapath.ServeDenseIdx (ReqArm deploySubs_dispatch healthReq bulkGzipReq)
open Datapath.ServeDenseReal (bulkDemoReq bulkDemoReqAnyHost)
open Datapath.ServeDenseFullReal (bulkBodyDense)
open Datapath.ServeHeadIdx (noPreambleB echoPostReq oldReq)
open Datapath.ServeMeteredHeadIdx (ipGateB rateGateB cleanPeer blockedPeer)
open Datapath.DenseStamps (preambledReq)
open Datapath.DenseStampsPlus5 (armB5 OffEdges plus5DenseArm_eq
  denseHeadBytesIdxPlus5 optionsBulkReq loginReq eventsReq appReq)
open Reactor.ServeConformant (ba_toList_eq ba_toList_length)

/-! ## 1. The new off-edges conjuncts (decidable, head-sized) -/

/-- **The plus6 off-edges conjuncts.** The decidable request-level facts under
which all the new stages are transparent: allowed method (the dispatch-scoped
`405` gate passes), no CL+TE conflict (the `400` gate passes), no `Range` list
(the multipart transform is the identity), target neither of the two new
routes (the gates pass, the stamps are no-ops). Every probe reads the
(head-sized) parsed request. -/
def OffEdges6 (req : Proto.Request) : Prop :=
  isAllowed req.method = true
  ∧ clTeConflict req = false
  ∧ rangesOf req = none
  ∧ ¬ req.target = welcomeTarget
  ∧ ¬ req.target = dashTarget

instance (req : Proto.Request) : Decidable (OffEdges6 req) := by
  unfold OffEdges6; infer_instance

/-! ## 2. The plus6 dense guard (one index-native parse) -/

/-- The plus6 dense guard: the plus5 guard's conjuncts AND the new off-edges
conjuncts, decided on ONE index-native head parse. -/
def armB6 (input : ByteArray) : Bool :=
  decide (0 < input.size)
    && decide (¬ input.size > deployConfig.maxHeaderBytes)
    && (match parseIndexNative (full input) with
        | .request _ req _ => decide (ReqArm req ∧ OffEdges req ∧ OffEdges6 req)
        | _ => false)

/-- **Guard soundness.** A firing plus6 guard fires the plus5 guard AND yields
the dispatched request with its new off-edges conjuncts. -/
theorem armB6_sound (input : ByteArray) (h : armB6 input = true) :
    armB5 input = true
    ∧ ∃ req rest, deploySubs input.toList = .dispatch req :: rest
        ∧ OffEdges6 req := by
  unfold armB6 at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hsz, hlen⟩, harm⟩ := h
  have hread : (full input).read = input.toList := by
    rw [read_eq_denote _ (full_wf _), denote_full, ← ba_toList_eq]
  cases hpo : parseIndexNative (full input) with
  | request n req ka =>
    rw [hpo] at harm
    obtain ⟨harm', hoff, hoff6⟩ := of_decide_eq_true harm
    constructor
    · unfold armB5
      rw [Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨hsz, hlen⟩, ?_⟩
      rw [hpo]
      exact decide_eq_true ⟨harm', hoff⟩
    · have hparse : Reactor.Config.h1ParseFn input.toList = .request n req ka := by
        rw [← hread, ← parseIndexNative_refines _ (full_wf _), hpo]
      have hlen' : ¬ input.toList.length > deployConfig.maxHeaderBytes := by
        rw [ba_toList_length]; exact of_decide_eq_true hlen
      have hne : input.toList.isEmpty = false := by
        have hpos : 0 < input.toList.length := by
          rw [ba_toList_length]; exact of_decide_eq_true hsz
        cases hl : input.toList with
        | nil => rw [hl] at hpos; exact absurd hpos (by simp)
        | cons a t => rfl
      obtain ⟨rest, hsub⟩ := deploySubs_dispatch input.toList n req ka hlen' hne hparse
      exact ⟨req, rest, hsub, hoff6⟩
  | reject n resp => rw [hpo] at harm; exact absurd harm (by simp)
  | incomplete => rw [hpo] at harm; exact absurd harm (by simp)
  | error => rw [hpo] at harm; exact absurd harm (by simp)

/-! ## 3. THE SERVE — the plus6 deployed-rung metered serve, dense `/bulk` arm -/

/-- **The plus6 dense-stamped deployed-rung metered serve.** A firing guard
emits the EXACT plus5 dense assembly (head + 1 MiB body, reused verbatim);
everything else — off-arm routes, the new routes (`/welcome`, `/dashboard`),
the new refusal shapes (`405`/`400`), multi-`Range` requests, refused
gates, preambled inputs — is the plus6 metered `List` fold verbatim. -/
def serveMeteredPlus6HeadIdx (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  if armB6 input && ipGateB peer && rateGateB seq.toNat && noPreambleB input then
    ByteArray.mk (denseHeadBytesIdxPlus5 input).toArray ++ bulkBodyDense
  else drorbServeMeteredPlus6 peer seq input

/-- **THE BYTE-IDENTITY.** For EVERY `(peer, seq, input)` the plus6 dense
serve produces the IDENTICAL bytes to the plus6 metered fold: a firing guard
composes the plus5 dense identity (`plus5DenseArm_eq`) with the plus6
conservation theorem (`plus6_collapse` — off the new edges the plus6 fold IS
the plus5 fold); everywhere else it IS the fold. -/
theorem serveMeteredPlus6HeadIdx_eq (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    serveMeteredPlus6HeadIdx peer seq input
      = drorbServeMeteredPlus6 peer seq input := by
  unfold serveMeteredPlus6HeadIdx
  cases hg : armB6 input && ipGateB peer && rateGateB seq.toNat
      && noPreambleB input with
  | false => rw [if_neg Bool.false_ne_true]
  | true =>
    rw [if_pos rfl]
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨harm6, hip⟩, hrate⟩, hnp⟩ := hg
    obtain ⟨harm5, req, rest, hsub, hoff6⟩ := armB6_sound input harm6
    obtain ⟨hmf, hclte, hr, hwt, hdt⟩ := hoff6
    -- the dense assembly is the plus5 fold's bytes (reused verbatim)
    have h5 := plus5DenseArm_eq peer seq input harm5 hip hrate hnp
    -- the dispatched request IS the metered context's request
    have hreq : (ctxOfMetered peer.toList seq.toNat input.toList).req = req :=
      ctxOf_req input.toList req rest hsub
    -- off the new edges the plus6 fold IS the plus5 fold
    have hcol := plus6_collapse (ctxOfMetered peer.toList seq.toNat input.toList)
      (by rw [hreq]; exact hwt)
      (by rw [hreq]; exact hdt)
      (by rw [hreq]; exact hclte)
      (by rw [hreq]; exact hmf)
      (by rw [hreq]; exact hr)
    have hserve : servePipelinePlus6Metered peer.toList seq.toNat input.toList
        = servePipelinePlus5Metered peer.toList seq.toNat input.toList := by
      show serialize (deployRespPlus6Of
          (ctxOfMetered peer.toList seq.toNat input.toList))
        = serialize (deployRespPlus5Of
          (ctxOfMetered peer.toList seq.toNat input.toList))
      rw [hcol]
    rw [h5]
    show ByteArray.mk (servePipelinePlus5Metered peer.toList seq.toNat
        input.toList).toArray
      = ByteArray.mk (servePipelinePlus6Metered peer.toList seq.toNat
          input.toList).toArray
    rw [hserve]

/-! ## 4. The RFC-conformant wrapper — the seam the deployed DEFAULT crosses -/

/-- **The deployed default's conformance wrapper over the plus6 dense serve.**

HOST-SYMBOL NOTE (honest): the host's default metered crossing is the FIXED C
symbol `drorb_serve_metered_plus5_dense_conformant` (its extern declaration
lives in the host serve seam, owned by another workstream). This export now
serves the PLUS6 fold under that symbol — same ABI, same conformance wrapper,
default-on. The plus5-accurate name is a named residual until the host seam
renames its declaration; the honest-named alias below exports the same serve
as `drorb_serve_metered_plus6_dense_conformant`. -/
-- drorb_serve_metered_plus5_dense_conformant is now exported by
-- Datapath.DenseStampsPlus7 (the plus7 fold took over the host default symbol).
def serveMeteredPlus6HeadIdxConformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  Reactor.ServeConformant.conformantServe
    (fun i => serveMeteredPlus6HeadIdx peer seq i) input

/-- **The wrapper preserves the byte-identity**: the plus6 dense conformant
serve equals `drorbServeMeteredPlus6Conformant` for EVERY `(peer, seq, input)`. -/
theorem serveMeteredPlus6HeadIdxConformant_eq (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    serveMeteredPlus6HeadIdxConformant peer seq input
      = drorbServeMeteredPlus6Conformant peer seq input := by
  unfold serveMeteredPlus6HeadIdxConformant
    Reactor.DeployPlus6.drorbServeMeteredPlus6Conformant
  rw [show (fun i => serveMeteredPlus6HeadIdx peer seq i)
        = (fun i => drorbServeMeteredPlus6 peer seq i) from
      funext (serveMeteredPlus6HeadIdx_eq peer seq)]

/-- A retired honest-named alias of the same serve (formerly the C export
`drorb_serve_metered_plus6_dense_conformant`; the `@[export]` was removed in
the consolidation). -/
def serveMeteredPlus6DenseConformantAlias (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  serveMeteredPlus6HeadIdxConformant peer seq input

/-! ## 5. Non-vacuity — the arm fires, every new edge genuinely refuses the
dense path, and the serve is byte-identical on every shape. -/

/-- `GET /welcome` — a NEW route; the dense guard must refuse (the `List` fold
answers it). -/
def welcomeReq : ByteArray :=
  "GET /welcome HTTP/1.1\r\nHost: x\r\nAccept-Language: de\r\n\r\n".toUTF8

/-- `GET /dashboard` — the other NEW route; the guard must refuse. -/
def dashReq : ByteArray := "GET /dashboard HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

/-- `DELETE /bulk` — a disallowed method (the `405` path); the guard must
refuse even on the `/bulk` target. -/
def deleteBulkReq : ByteArray := "DELETE /bulk HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

/-- `GET /bulk` announcing both framings — the smuggling shape (`400`). -/
def clteBulkReq : ByteArray :=
  "GET /bulk HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\n".toUTF8

/-- A multi-`Range` `/bulk` request — the multipart `206` path; the guard must
refuse (the answer is a DIFFERENT byte string than the dense 200). -/
def rangeBulkReq : ByteArray :=
  "GET /bulk HTTP/1.1\r\nHost: x\r\nRange: bytes=0-1,3-4\r\n\r\n".toUTF8

-- The plus6 dense guard genuinely fires on the real `/bulk` request…
#guard armB6 bulkDemoReq && ipGateB cleanPeer && rateGateB 0
        && noPreambleB bulkDemoReq
-- …and genuinely refuses every NEW on-edge shape (each still armB5-armed or
-- route-shaped, so the refusal is the NEW conjuncts' doing).
#guard !(armB6 welcomeReq)
#guard !(armB6 dashReq)
#guard !(armB6 deleteBulkReq)
#guard !(armB6 clteBulkReq)
#guard !(armB6 rangeBulkReq)
-- …the multi-range and method probes fire the OLD guard (the refusal above is
-- genuinely the new conjuncts, not an armB5 artifact).
#guard armB5 rangeBulkReq
#guard !(armB5 welcomeReq)
-- Byte-identity to the plus6 metered fold on every shape: on-arm, off-arm,
-- the new routes, the new refusals, multi-range, the plus5 edges,
-- gate-refused, preambled.
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 bulkDemoReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 bulkDemoReqAnyHost).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 bulkDemoReqAnyHost).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 healthReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 healthReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 welcomeReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 welcomeReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 dashReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 dashReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 deleteBulkReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 deleteBulkReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 clteBulkReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 clteBulkReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 rangeBulkReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 rangeBulkReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 bulkGzipReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 bulkGzipReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 echoPostReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 echoPostReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 oldReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 oldReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 optionsBulkReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 optionsBulkReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 loginReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 loginReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 eventsReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 eventsReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 appReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 appReq).data.toList
#guard (serveMeteredPlus6HeadIdx blockedPeer 0 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus6 blockedPeer 0 bulkDemoReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 8 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 8 bulkDemoReq).data.toList
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 preambledReq).data.toList
        == (drorbServeMeteredPlus6 cleanPeer 0 preambledReq).data.toList
-- The dense arm fires (1 MiB body); refusal shapes stay head-sized.
#guard (serveMeteredPlus6HeadIdx cleanPeer 0 bulkDemoReq).size > 1048576
#guard (serveMeteredPlus6HeadIdx blockedPeer 0 bulkDemoReq).size < 1024
-- Through the conformance wrapper: byte-identical to the plus6 conformant
-- default, and the dense arm survives the wrapper (> 1 MiB).
#guard (serveMeteredPlus6HeadIdxConformant cleanPeer 0 bulkDemoReqAnyHost).data.toList
        == (drorbServeMeteredPlus6Conformant cleanPeer 0 bulkDemoReqAnyHost).data.toList
#guard (serveMeteredPlus6HeadIdxConformant cleanPeer 0 bulkDemoReqAnyHost).size > 1048576
#guard (serveMeteredPlus6HeadIdxConformant cleanPeer 0 welcomeReq).data.toList
        == (drorbServeMeteredPlus6Conformant cleanPeer 0 welcomeReq).data.toList
#guard (serveMeteredPlus6HeadIdxConformant cleanPeer 0 dashReq).data.toList
        == (drorbServeMeteredPlus6Conformant cleanPeer 0 dashReq).data.toList

end Datapath.DenseStampsPlus6

#print axioms Datapath.DenseStampsPlus6.armB6_sound
#print axioms Datapath.DenseStampsPlus6.serveMeteredPlus6HeadIdx_eq
#print axioms Datapath.DenseStampsPlus6.serveMeteredPlus6HeadIdxConformant_eq
