import Reactor.DeployPlus8
import Datapath.DenseStampsPlus6

/-!
# Datapath.DenseStampsPlus8 — the DEPLOYED DEFAULT moves to the plus8 fold,
dense `/bulk` arm intact

`Reactor.DeployPlus8` extends the deployed default with the un-inerted
(`/bulk`-excluded) `Vary` stamp and the two new refusal gates (`414` / `406`).
This module moves the DEPLOYED DEFAULT to that fold while keeping the dense
`/bulk` datapath byte-identical:

* `OffEdges8` — the ONE new off-edges conjunct: under the target budget (the
  `414` gate passes). The other new edges are already excluded by the inherited
  facts: the arm's own `targetSegments = ["bulk"]` makes the `Vary` stamp the
  identity, and the plus6 conjuncts' `target ≠ /welcome` makes the `406` gate
  pass.
* `armB8` — the plus8 dense guard: ONE index-native head parse deciding the
  plus5 arm, the plus6 off-edges AND the new conjunct.
* `serveMeteredPlus8HeadIdx` — the deployed-rung metered serve: a firing
  guard emits the EXACT plus5 dense assembly (reused verbatim); everything
  else is the plus8 metered `List` fold.
* `serveMeteredPlus8HeadIdx_eq` — **the byte-identity**: for EVERY
  `(peer, seq, input)` it equals `drorbServeMeteredPlus8`. The firing case
  composes the plus5 dense identity (`plus5DenseArm_eq`) with the plus8 and
  plus6 conservation theorems (on the datapath target, off every edge, the
  plus8 fold IS the plus5 fold).
* `serveMeteredPlus8HeadIdxConformant` — the RFC-conformant wrapper, proven
  equal to `drorbServeMeteredPlus8Conformant` for every input.

HOST-SYMBOL NOTE (honest): the host's default metered crossing is the FIXED C
symbol `drorb_serve_metered_plus5_dense_conformant` (its extern declaration
lives in the host serve seam, owned by another workstream). The plus6 module
RELEASED that export this session (mid-transition to the in-flight plus7
wave, whose fold has not landed — the tree was left with NO owner of the
default symbol, i.e. unlinkable). This module now owns it — the symbol serves
the PLUS8 fold, same ABI, same conformance wrapper, default-on; it re-parents
onto the plus7 fold by one import + one collapse-call change when that wave
lands. The plus5-accurate name remains a named residual until the host seam
renames its declaration; the honest-named alias below exports the same serve
as `drorb_serve_metered_plus8_dense_conformant`.

Residuals (named): the guard performs one extra head-sized decide per request
over the plus6 guard (index-native, never the body); an over-budget or
all-`q=0`-negotiating request leaves the dense arm (correct — its answer is a
refusal, a different byte string, served by the `List` fold).
-/

namespace Datapath.DenseStampsPlus8

open Proto (Bytes)
open Reactor (Response serialize)
open Reactor.Pipeline (Ctx runPipeline)
open Reactor.Deploy
open Reactor.DeployPlus5 (servePipelinePlus5Metered deployRespPlus5Of)
open Reactor.DeployPlus8 (deployStagesPlus8 drorbServeMeteredPlus8
  drorbServeMeteredPlus8Conformant servePipelinePlus8Metered
  deployRespPlus8Of plus8_collapse isBulkTarget isBulkTarget_of_segs bulkSegs)
open Reactor.Stage.MethodFilter (isAllowed)
open Reactor.Stage.ClTeGuard (clTeConflict)
open Reactor.Stage.MultiRange (rangesOf)
open Reactor.Stage.ContentLanguage (welcomeTarget)
open Reactor.Stage.Dashboard (dashTarget)
open Reactor.Stage.UriTooLong (overCap)
open Datapath.SpanBytes (full full_wf read_eq_denote denote_full
  parseIndexNative parseIndexNative_refines)
open Datapath.ServeDenseIdx (ReqArm deploySubs_dispatch healthReq bulkGzipReq)
open Datapath.ServeDenseReal (bulkDemoReq bulkDemoReqAnyHost BulkArm)
open Datapath.ServeDenseFullReal (bulkBodyDense)
open Datapath.ServeHeadIdx (noPreambleB echoPostReq oldReq)
open Datapath.ServeMeteredHeadIdx (ipGateB rateGateB cleanPeer blockedPeer)
open Datapath.DenseStamps (preambledReq)
open Datapath.DenseStampsPlus5 (armB5 OffEdges plus5DenseArm_eq
  denseHeadBytesIdxPlus5 optionsBulkReq loginReq eventsReq appReq)
open Datapath.DenseStampsPlus6 (OffEdges6 welcomeReq dashReq
  deleteBulkReq clteBulkReq rangeBulkReq)
open Reactor.ServeConformant (ba_toList_eq ba_toList_length)

/-! ## 1. The new off-edges conjunct (decidable, head-sized) -/

/-- **The plus8 off-edges conjunct.** Under the target budget (the `414` gate
passes). The `Vary` exclusion needs no conjunct (the arm itself pins
`targetSegments = ["bulk"]`), nor does the `406` gate (the plus6 conjuncts pin
the target off `/welcome`). -/
def OffEdges8 (req : Proto.Request) : Prop :=
  overCap req = false

instance (req : Proto.Request) : Decidable (OffEdges8 req) := by
  unfold OffEdges8; infer_instance

/-! ## 2. The plus8 dense guard (one index-native parse) -/

/-- The plus8 dense guard: the plus5 arm, every inherited off-edges conjunct
AND the new one, decided on ONE index-native head parse. -/
def armB8 (input : ByteArray) : Bool :=
  decide (0 < input.size)
    && decide (¬ input.size > deployConfig.maxHeaderBytes)
    && (match parseIndexNative (full input) with
        | .request _ req _ =>
          decide (ReqArm req ∧ OffEdges req ∧ OffEdges6 req ∧ OffEdges8 req)
        | _ => false)

/-- **Guard soundness.** A firing plus8 guard fires the plus5 guard AND yields
the dispatched request with the arm fact and every off-edges conjunct. -/
theorem armB8_sound (input : ByteArray) (h : armB8 input = true) :
    armB5 input = true
    ∧ ∃ req rest, deploySubs input.toList = .dispatch req :: rest
        ∧ ReqArm req ∧ OffEdges6 req ∧ OffEdges8 req := by
  unfold armB8 at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hsz, hlen⟩, harm⟩ := h
  have hread : (full input).read = input.toList := by
    rw [read_eq_denote _ (full_wf _), denote_full, ← ba_toList_eq]
  cases hpo : parseIndexNative (full input) with
  | request n req ka =>
    rw [hpo] at harm
    obtain ⟨harm', hoff, hoff6, hoff8⟩ := of_decide_eq_true harm
    constructor
    · unfold Datapath.DenseStampsPlus5.armB5
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
      exact ⟨req, rest, hsub, harm', hoff6, hoff8⟩
  | reject n resp => rw [hpo] at harm; exact absurd harm (by simp)
  | incomplete => rw [hpo] at harm; exact absurd harm (by simp)
  | error => rw [hpo] at harm; exact absurd harm (by simp)

/-! ## 3. THE SERVE — the plus8 deployed-rung metered serve, dense `/bulk` arm -/

/-- **The plus8 dense-stamped deployed-rung metered serve.** A firing guard
emits the EXACT plus5 dense assembly (head + 1 MiB body, reused verbatim);
everything else — off-arm routes, the `Vary`-stamped routes, the new refusal
shapes (`414`/`406`), refused gates, preambled inputs — is the plus8 metered
`List` fold verbatim. -/
@[export drorb_serve_metered_plus8_head_idx]
def serveMeteredPlus8HeadIdx (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  if armB8 input && ipGateB peer && rateGateB seq.toNat && noPreambleB input then
    ByteArray.mk (denseHeadBytesIdxPlus5 input).toArray ++ bulkBodyDense
  else drorbServeMeteredPlus8 peer seq input

/-- The arm's `targetSegments = ["bulk"]` fact, extracted from `BulkArm`
(conjunct 9; the arm context carries exactly the parsed request). -/
theorem reqArm_bulkSegs (req : Proto.Request) (h : ReqArm req) :
    Reactor.App.targetSegments req.target = bulkSegs := by
  obtain ⟨_, _, _, _, _, _, _, _, hsegs, _, _⟩ := h
  simpa [Datapath.ServeDenseIdx.reqCtx, Reactor.DeployPlus8.bulkSegs]
    using hsegs

/-- **THE BYTE-IDENTITY.** For EVERY `(peer, seq, input)` the plus8 dense
serve produces the IDENTICAL bytes to the plus8 metered fold: a firing guard
composes the plus5 dense identity (`plus5DenseArm_eq`) with the plus8 and
plus6 conservation theorems; everywhere else it IS the fold. -/
theorem serveMeteredPlus8HeadIdx_eq (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    serveMeteredPlus8HeadIdx peer seq input
      = drorbServeMeteredPlus8 peer seq input := by
  unfold serveMeteredPlus8HeadIdx
  cases hg : armB8 input && ipGateB peer && rateGateB seq.toNat
      && noPreambleB input with
  | false => rw [if_neg Bool.false_ne_true]
  | true =>
    rw [if_pos rfl]
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨harm8, hip⟩, hrate⟩, hnp⟩ := hg
    obtain ⟨harm5, req, rest, hsub, harm, hoff6, hoff8⟩ :=
      armB8_sound input harm8
    obtain ⟨hmf, hclte, hr, hwt, hdt⟩ := hoff6
    -- the dense assembly is the plus5 fold's bytes (reused verbatim)
    have h5 := plus5DenseArm_eq peer seq input harm5 hip hrate hnp
    -- the dispatched request IS the metered context's request
    have hreq : (ctxOfMetered peer.toList seq.toNat input.toList).req = req :=
      ctxOf_req input.toList req rest hsub
    -- plus8 → plus6 (on the datapath target, off the new edges)
    have hb : isBulkTarget (ctxOfMetered peer.toList seq.toNat input.toList)
        = true := by
      apply isBulkTarget_of_segs
      rw [hreq]
      exact reqArm_bulkSegs req harm
    have hcol8 := plus8_collapse
      (ctxOfMetered peer.toList seq.toNat input.toList)
      hb
      (by rw [hreq]; exact hoff8)
      (by rw [hreq]; exact hwt)
    -- plus6 → plus5 (the plus6 conservation theorem, off its edges)
    have hcol6 := Reactor.DeployPlus6.plus6_collapse
      (ctxOfMetered peer.toList seq.toNat input.toList)
      (by rw [hreq]; exact hwt)
      (by rw [hreq]; exact hdt)
      (by rw [hreq]; exact hclte)
      (by rw [hreq]; exact hmf)
      (by rw [hreq]; exact hr)
    have hserve : servePipelinePlus8Metered peer.toList seq.toNat input.toList
        = servePipelinePlus5Metered peer.toList seq.toNat input.toList := by
      show serialize (deployRespPlus8Of
          (ctxOfMetered peer.toList seq.toNat input.toList))
        = serialize (deployRespPlus5Of
          (ctxOfMetered peer.toList seq.toNat input.toList))
      rw [hcol8, hcol6]
    rw [h5]
    show ByteArray.mk (servePipelinePlus5Metered peer.toList seq.toNat
        input.toList).toArray
      = ByteArray.mk (servePipelinePlus8Metered peer.toList seq.toNat
          input.toList).toArray
    rw [hserve]

/-! ## 4. The RFC-conformant wrapper — the seam the deployed DEFAULT crosses -/

/-- **The plus8 dense conformance wrapper** — the deployed serve INNER. The
host default symbol `drorb_serve_metered_plus5_dense_conformant` was RE-HOMED
this session to `Reactor.DeployPipeline.serveMeteredPipelineConformant`, whose
body is this exact function (byte-identical by construction); this def stays as
the proven dense inner and keeps its honest-named alias export below. -/
def serveMeteredPlus8HeadIdxConformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  Reactor.ServeConformant.conformantServe
    (fun i => serveMeteredPlus8HeadIdx peer seq i) input

/-- **The wrapper preserves the byte-identity**: the plus8 dense conformant
serve equals `drorbServeMeteredPlus8Conformant` for EVERY `(peer, seq, input)`. -/
theorem serveMeteredPlus8HeadIdxConformant_eq (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) :
    serveMeteredPlus8HeadIdxConformant peer seq input
      = drorbServeMeteredPlus8Conformant peer seq input := by
  unfold serveMeteredPlus8HeadIdxConformant
    Reactor.DeployPlus8.drorbServeMeteredPlus8Conformant
  rw [show (fun i => serveMeteredPlus8HeadIdx peer seq i)
        = (fun i => drorbServeMeteredPlus8 peer seq i) from
      funext (serveMeteredPlus8HeadIdx_eq peer seq)]

/-- The honest-named alias of the SAME deployed serve (the host's next
re-point target). -/
@[export drorb_serve_metered_plus8_dense_conformant]
def serveMeteredPlus8DenseConformantAlias (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  serveMeteredPlus8HeadIdxConformant peer seq input

/-! ## 5. Non-vacuity — the arm fires, every new edge genuinely refuses or
leaves the dense path, and the serve is byte-identical on every shape. -/

/-- A `Vary`-stamped route (`GET /health`) — off-arm; byte-identity must hold
and the answer must carry the stamp. -/
def healthReq8 : ByteArray := "GET /health HTTP/1.1\r\nHost: x\r\n\r\n".toUTF8

/-- The all-`q=0` negotiated-route shape — the `406` path. -/
def q0WelcomeReq8 : ByteArray :=
  "GET /welcome HTTP/1.1\r\nHost: x\r\nAccept-Language: de;q=0, en;q=0, fr;q=0\r\n\r\n".toUTF8

/-- An over-budget target — the `414` path. -/
def longUriReq8 : ByteArray :=
  (("GET /" ++ String.mk (List.replicate 2500 'a') ++ " HTTP/1.1\r\nHost: x\r\n\r\n").toUTF8)

-- The plus8 dense guard genuinely fires on the real `/bulk` request…
#guard armB8 bulkDemoReq && ipGateB cleanPeer && rateGateB 0
        && noPreambleB bulkDemoReq
-- …and genuinely refuses the new refusal shapes…
#guard !(armB8 longUriReq8)
#guard !(armB8 q0WelcomeReq8)
-- …while the plus6/plus7-edge shapes stay refused as before.
#guard !(armB8 welcomeReq)
#guard !(armB8 dashReq)
#guard !(armB8 deleteBulkReq)
#guard !(armB8 clteBulkReq)
#guard !(armB8 rangeBulkReq)
-- Byte-identity to the plus8 metered fold on every shape.
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 bulkDemoReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 bulkDemoReqAnyHost).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 bulkDemoReqAnyHost).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 healthReq8).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 healthReq8).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 longUriReq8).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 longUriReq8).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 q0WelcomeReq8).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 q0WelcomeReq8).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 welcomeReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 welcomeReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 dashReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 dashReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 deleteBulkReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 deleteBulkReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 clteBulkReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 clteBulkReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 rangeBulkReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 rangeBulkReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 bulkGzipReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 bulkGzipReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 echoPostReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 echoPostReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 oldReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 oldReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 optionsBulkReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 optionsBulkReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 loginReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 loginReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 eventsReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 eventsReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 appReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 appReq).data.toList
#guard (serveMeteredPlus8HeadIdx blockedPeer 0 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus8 blockedPeer 0 bulkDemoReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 8 bulkDemoReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 8 bulkDemoReq).data.toList
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 preambledReq).data.toList
        == (drorbServeMeteredPlus8 cleanPeer 0 preambledReq).data.toList
-- The dense arm fires (1 MiB body); refusal shapes stay head-sized.
#guard (serveMeteredPlus8HeadIdx cleanPeer 0 bulkDemoReq).size > 1048576
#guard (serveMeteredPlus8HeadIdx blockedPeer 0 bulkDemoReq).size < 1024
-- Through the conformance wrapper: byte-identical to the plus8 conformant
-- default, and the dense arm survives the wrapper (> 1 MiB).
#guard (serveMeteredPlus8HeadIdxConformant cleanPeer 0 bulkDemoReqAnyHost).data.toList
        == (drorbServeMeteredPlus8Conformant cleanPeer 0 bulkDemoReqAnyHost).data.toList
#guard (serveMeteredPlus8HeadIdxConformant cleanPeer 0 bulkDemoReqAnyHost).size > 1048576
#guard (serveMeteredPlus8HeadIdxConformant cleanPeer 0 healthReq8).data.toList
        == (drorbServeMeteredPlus8Conformant cleanPeer 0 healthReq8).data.toList
#guard (serveMeteredPlus8HeadIdxConformant cleanPeer 0 longUriReq8).data.toList
        == (drorbServeMeteredPlus8Conformant cleanPeer 0 longUriReq8).data.toList

end Datapath.DenseStampsPlus8

#print axioms Datapath.DenseStampsPlus8.armB8_sound
#print axioms Datapath.DenseStampsPlus8.serveMeteredPlus8HeadIdx_eq
#print axioms Datapath.DenseStampsPlus8.serveMeteredPlus8HeadIdxConformant_eq
